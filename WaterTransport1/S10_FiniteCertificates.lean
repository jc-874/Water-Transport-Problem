import WaterTransport1.S02_Strategies
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Data.List.Sublists

/-!
# Paper 1: exact certificates for the finite examples

Reading order: generic rational checkers and soundness; connected-set coverage;
the spider's three-step bound; an invariant polytope for the linear reward example.
Rational execution agrees with the shared real model. Finite certificates are
checked in Lean, and the polytope implications use exact linear arithmetic.
External searches can suggest data but are not part of the trusted proof.
-/

namespace WaterTransport

variable {V : Type*} [Fintype V] [DecidableEq V]

/-!
## Generic finite checkers and soundness

The checker quantifies over a supplied move list. Graph legality and completeness of that list are separate obligations.
-/

/-- Check all move words of length at most `k`, testing the option to stop at every depth. -/
def checkBound (moves : List (Finset V)) (f : (V → ℚ) → ℚ) (B : ℚ) :
    ℕ → (V → ℚ) → Bool
  | 0, w => decide (f w ≤ B)
  | k + 1, w => decide (f w ≤ B) &&
      moves.all (fun S => checkBound moves f B k (averageQ S w))

/-- A successful check bounds every word within the horizon using moves from the supplied list. -/
theorem checkBound_sound (moves : List (Finset V)) (f : (V → ℚ) → ℚ) (B : ℚ)
    (k : ℕ) (w : V → ℚ) (hc : checkBound moves f B k w = true)
    (σ : Strategy V) (hm : ∀ S ∈ σ, S ∈ moves) (hlen : σ.length ≤ k) :
    f (runQ σ w) ≤ B := by
  induction k generalizing σ w with
  | zero =>
    have hnil : σ = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    subst σ
    exact of_decide_eq_true hc
  | succ k ih =>
    have hc' := Bool.and_eq_true_iff.mp hc
    cases σ with
    | nil => exact of_decide_eq_true hc'.1
    | cons S σ =>
      exact ih _ ((List.all_eq_true.mp hc'.2) S (hm S (by simp))) σ
        (fun T hT => hm T (by simp [hT])) (by simpa using hlen)

/-- For repetition-free words, erase a move after using it and enumerate distinct remaining moves. -/
def checkDistinct (f : (V → ℚ) → ℚ) (B : ℚ) :
    ℕ → List (Finset V) → (V → ℚ) → Bool
  | 0, _, w => decide (f w ≤ B)
  | k + 1, moves, w => decide (f w ≤ B) &&
      moves.all (fun S => checkDistinct f B k (moves.erase S) (averageQ S w))

/-- A successful distinct-move check bounds every duplicate-free word from the supplied list within the horizon. -/
theorem checkDistinct_sound (f : (V → ℚ) → ℚ) (B : ℚ) (k : ℕ)
    (moves : List (Finset V)) (w : V → ℚ) (hc : checkDistinct f B k moves w = true)
    (σ : Strategy V) (hm : ∀ S ∈ σ, S ∈ moves) (hlen : σ.length ≤ k) (hd : σ.Nodup) :
    f (runQ σ w) ≤ B := by
  induction k generalizing σ moves w with
  | zero =>
    have hnil : σ = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    subst σ
    exact of_decide_eq_true hc
  | succ k ih =>
    have hc' := Bool.and_eq_true_iff.mp hc
    cases σ with
    | nil => exact of_decide_eq_true hc'.1
    | cons S σ =>
      have hd' := List.nodup_cons.mp hd
      apply ih (moves.erase S) _ ((List.all_eq_true.mp hc'.2) S (hm S (by simp))) σ
        ?_ (by simpa using hlen) hd'.2
      intro T hT
      have hne : T ≠ S := fun h => hd'.1 (h ▸ hT)
      exact (List.mem_erase_of_ne hne).mpr (hm T (by simp [hT]))

/-!
## Preparation: finite certificates for connected selected sets

Use adjacency closure and cut crossings to certify coverage of legal moves.
-/

/-- Inside a connected selected set, a nonempty adjacency-closed part is the whole set.
This gives a finite connectivity obstruction without enumerating paths. -/
private theorem IsLegalMove.subset_of_closed {G : SimpleGraph V} {S T : Finset V}
    (hS : IsLegalMove G S) (u : V) (hu : u ∈ S) (huT : u ∈ T)
    (hclosed : ∀ a ∈ T, ∀ b ∈ S, G.Adj a b → b ∈ T) : S ⊆ T := by
  have hwalk : ∀ a b : (S : Set V), (G.induce (S : Set V)).Reachable a b →
      a.val ∈ T → b.val ∈ T := by
    intro a b hp
    obtain ⟨p⟩ := hp
    induction p with
    | nil => exact id
    | @cons a b c hadj p ih =>
      intro ha
      exact ih (hclosed a.val ha b.val b.property hadj)
  intro v hv
  exact hwalk ⟨u, hu⟩ ⟨v, hv⟩ (hS.2.preconnected _ _) huT

/-- A connected selected set meeting both sides of a cut contains an edge crossing the cut. -/
private theorem IsLegalMove.crosses_cut {G : SimpleGraph V} {S T : Finset V}
    (hS : IsLegalMove G S) (u v : V) (hu : u ∈ S) (hv : v ∈ S)
    (huT : u ∈ T) (hvT : v ∉ T) :
    ∃ a ∈ S, ∃ b ∈ S, a ∈ T ∧ b ∉ T ∧ G.Adj a b := by
  have hwalk : ∀ a b : (S : Set V), (G.induce (S : Set V)).Walk a b →
      a.val ∈ T → b.val ∉ T →
      ∃ c ∈ S, ∃ d ∈ S, c ∈ T ∧ d ∉ T ∧ G.Adj c d := by
    intro a b p
    induction p with
    | nil => intro ha hb; exact (hb ha).elim
    | @cons a b c hadj p ih =>
      intro ha hc
      by_cases hb : b.val ∈ T
      · exact ih hb hc
      · exact ⟨a.val, a.property, b.val, b.property, ha, hb, hadj⟩
  obtain ⟨p⟩ := hS.2.preconnected ⟨u, hu⟩ ⟨v, hv⟩
  exact hwalk _ _ p huT hvT

/-!
## Preparation: cached coordinate checking

Use rational vectors to evaluate deep finite certificates efficiently, with a soundness theorem relating them to runQ.
-/

/-- Cache all rational coordinates in a vector to avoid repeatedly expanding earlier averages. -/
private def averageVec {n : ℕ} (S : Finset (Fin n)) (w : Vector ℚ n) : Vector ℚ n :=
  Vector.ofFn (averageQ S (fun v => w[v.val]))

private def checkCoordinateBound {n : ℕ} (moves : List (Finset (Fin n))) (x : Fin n) (B : ℚ) :
    ℕ → Vector ℚ n → Bool
  | 0, w => decide (w[x.val] ≤ B)
  | 1, w => decide (w[x.val] ≤ B) &&
      moves.all (fun S => decide (averageQ S (fun v => w[v.val]) x ≤ B))
  | k + 2, w => decide (w[x.val] ≤ B) &&
      moves.all (fun S => checkCoordinateBound moves x B (k + 1) (averageVec S w))

/-- At the final level only the target coordinate is needed; prove agreement with full vector recursion. -/
private theorem checkCoordinateBound_succ {n : ℕ} (moves : List (Finset (Fin n))) (x : Fin n) (B : ℚ)
    (k : ℕ) (w : Vector ℚ n) :
    checkCoordinateBound moves x B (k + 1) w = (decide (w[x.val] ≤ B) &&
      moves.all (fun S => checkCoordinateBound moves x B k (averageVec S w))) := by
  cases k with
  | zero => simp only [checkCoordinateBound, averageVec, Vector.getElem_ofFn, Fin.eta]
  | succ k => rfl

theorem checkCoordinateBound_sound {n : ℕ} (moves : List (Finset (Fin n))) (x : Fin n) (B : ℚ)
    (k : ℕ) (w : Vector ℚ n) (hc : checkCoordinateBound moves x B k w = true)
    (σ : Strategy (Fin n)) (hm : ∀ S ∈ σ, S ∈ moves) (hlen : σ.length ≤ k) :
    runQ σ (fun v => w[v.val]) x ≤ B := by
  induction k generalizing σ w with
  | zero =>
    have hnil : σ = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    subst σ
    exact of_decide_eq_true hc
  | succ k ih =>
    rw [checkCoordinateBound_succ] at hc
    have hc' := Bool.and_eq_true_iff.mp hc
    cases σ with
    | nil => exact of_decide_eq_true hc'.1
    | cons S σ =>
      simpa only [averageVec, Vector.getElem_ofFn, Fin.eta, runQ] using
        ih _ ((List.all_eq_true.mp hc'.2) S (hm S (by simp))) σ
          (fun T hT => hm T (by simp [hT])) (by simpa using hlen)

end WaterTransport

/-!
## Spider certificate: coverage of all nontrivial legal moves

The tree's eight edges give eight cuts. A connected set meeting both sides must
contain both endpoints of the cut edge. These tests certify coverage by the
listed 52 nontrivial moves; Lean checks the finite subset certificate.
-/

namespace WaterTransport.Examples

set_option cbv.maxSteps 5000000
set_option Elab.async false

def spiderEdges : Finset (Fin 9 × Fin 9) :=
  {(0, 1), (1, 2), (2, 3), (3, 4), (0, 5), (5, 6), (0, 7), (7, 8)}

/-- Symmetrize the listed edges and remove loops using `SimpleGraph.fromRel`. -/
def spiderGraph : SimpleGraph (Fin 9) :=
  SimpleGraph.fromRel fun u v => (u, v) ∈ spiderEdges

/-- The explicit list of 52 nontrivial connected averaging sets for Example 4.2. -/
def spiderMoves : List (Finset (Fin 9)) :=
  [{0, 1},
   {1, 2},
   {0, 1, 2},
   {2, 3},
   {1, 2, 3},
   {0, 1, 2, 3},
   {3, 4},
   {2, 3, 4},
   {1, 2, 3, 4},
   {0, 1, 2, 3, 4},
   {0, 5},
   {0, 1, 5},
   {0, 1, 2, 5},
   {0, 1, 2, 3, 5},
   {0, 1, 2, 3, 4, 5},
   {5, 6},
   {0, 5, 6},
   {0, 1, 5, 6},
   {0, 1, 2, 5, 6},
   {0, 1, 2, 3, 5, 6},
   {0, 1, 2, 3, 4, 5, 6},
   {0, 7},
   {0, 1, 7},
   {0, 1, 2, 7},
   {0, 1, 2, 3, 7},
   {0, 1, 2, 3, 4, 7},
   {0, 5, 7},
   {0, 1, 5, 7},
   {0, 1, 2, 5, 7},
   {0, 1, 2, 3, 5, 7},
   {0, 1, 2, 3, 4, 5, 7},
   {0, 5, 6, 7},
   {0, 1, 5, 6, 7},
   {0, 1, 2, 5, 6, 7},
   {0, 1, 2, 3, 5, 6, 7},
   {0, 1, 2, 3, 4, 5, 6, 7},
   {7, 8},
   {0, 7, 8},
   {0, 1, 7, 8},
   {0, 1, 2, 7, 8},
   {0, 1, 2, 3, 7, 8},
   {0, 1, 2, 3, 4, 7, 8},
   {0, 5, 7, 8},
   {0, 1, 5, 7, 8},
   {0, 1, 2, 5, 7, 8},
   {0, 1, 2, 3, 5, 7, 8},
   {0, 1, 2, 3, 4, 5, 7, 8},
   {0, 5, 6, 7, 8},
   {0, 1, 5, 6, 7, 8},
   {0, 1, 2, 5, 6, 7, 8},
   {0, 1, 2, 3, 5, 6, 7, 8},
   {0, 1, 2, 3, 4, 5, 6, 7, 8}]

def spiderWeightsQ : Fin 9 → ℚ := fun v =>
  if v = 0 then 101 / 10 else
  if v = 1 then 10 else
  if v = 2 then 0 else
  if v = 3 then 100 else
  if v = 4 then 10000 else
  if v = 5 then 98 / 10 else
  if v = 6 then 1000 else
  if v = 7 then 101 / 10 else 9


instance spiderAdjDecidable : DecidableRel spiderGraph.Adj := fun u v => by
  change Decidable (u ≠ v ∧ ((u, v) ∈ spiderEdges ∨ (v, u) ∈ spiderEdges))
  infer_instance

/-- Each triple records an edge towards the root and the subtree separated by its removal. -/
private def cuts : List (Fin 9 × Fin 9 × Finset (Fin 9)) :=
  [(1, 0, {1, 2, 3, 4}), (2, 1, {2, 3, 4}), (3, 2, {3, 4}), (4, 3, {4}),
   (5, 0, {5, 6}), (6, 5, {6}), (7, 0, {7, 8}), (8, 7, {8})]

private def cutCondition (S : Finset (Fin 9)) (e : Fin 9 × Fin 9 × Finset (Fin 9)) : Bool :=
  decide ((S ∩ e.2.2).Nonempty → (S \ e.2.2).Nonempty → e.1 ∈ S ∧ e.2.1 ∈ S)

private theorem cut_edges : cuts.all (fun e => decide
    (∀ a ∈ e.2.2, ∀ b : Fin 9, b ∉ e.2.2 → spiderGraph.Adj a b → a = e.1 ∧ b = e.2.1)) = true := by
  decide +kernel

private theorem connected_cuts (S : Finset (Fin 9)) (hS : IsLegalMove spiderGraph S) :
    cuts.all (cutCondition S) = true := by
  apply List.all_eq_true.mpr
  intro e he
  unfold cutCondition
  apply decide_eq_true
  intro hleft hright
  obtain ⟨u, hu⟩ := hleft
  obtain ⟨v, hv⟩ := hright
  obtain ⟨hu, huT⟩ := Finset.mem_inter.mp hu
  obtain ⟨hv, hvT⟩ := Finset.mem_sdiff.mp hv
  obtain ⟨a, ha, b, hb, haT, hbT, hadj⟩ :=
    hS.crosses_cut u v hu hv huT hvT
  have he' := of_decide_eq_true ((List.all_eq_true.mp cut_edges) e he)
  obtain ⟨rfl, rfl⟩ := he' a haT b hbT hadj
  exact ⟨ha, hb⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem shape_certificate : ((List.finRange 9).sublists.map List.toFinset).all
    (fun S => decide (2 ≤ S.card → cuts.all (cutCondition S) = true → S ∈ spiderMoves)) = true := by
  decide +kernel

/-- Every legal selected set of cardinality at least two occurs in `spiderMoves`. -/
theorem spider_moves_complete (S : Finset (Fin 9))
    (hS : IsLegalMove spiderGraph S) (hcard : 2 ≤ S.card) : S ∈ spiderMoves := by
  have hmem : S ∈ (List.finRange 9).sublists.map List.toFinset := by
    apply List.mem_map.mpr
    refine ⟨(List.finRange 9).filter (fun v => v ∈ S),
      List.mem_sublists.mpr (List.filter_sublist), ?_⟩
    ext v
    simp
  exact (of_decide_eq_true ((List.all_eq_true.mp shape_certificate) S hmem))
    hcard (connected_cuts S hS)

end WaterTransport.Examples


/-!
## Spider certificate: the three-step target bound

Split on the 52 possible first nontrivial moves, then check at most two further
moves in each branch. All rational inequalities are verified by Lean's kernel.
-/

namespace WaterTransport.Examples

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

private theorem branches (i : Fin spiderMoves.length) :
    checkCoordinateBound spiderMoves 0 (806666 / 375) 2
      (averageVec spiderMoves[i] (Vector.ofFn spiderWeightsQ)) = true := by
  fin_cases i <;> decide +kernel

/-- Kernel-checked rational certificate for the upper bound 806666/375 through three moves. -/
theorem spider_three_certificate :
    checkCoordinateBound spiderMoves 0 (806666 / 375) 3
      (Vector.ofFn spiderWeightsQ) = true := by
  rw [checkCoordinateBound_succ]
  apply Bool.and_eq_true_iff.mpr
  refine ⟨by decide +kernel, List.all_eq_true.mpr ?_⟩
  intro S hS
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hS
  exact branches i

end WaterTransport.Examples


/-!
## Example 4.3 certificate: an invariant reward polytope

The certificate consists of 22 linear inequalities and total mass 111.
All seven nontrivial star moves preserve it. The example file verifies membership
of the initial state and propagates this invariant through an arbitrary strategy.
Exact real arithmetic proves the objective bound for all finite lengths.
-/

namespace WaterTransport.RewardCertificate

set_option linter.unnecessarySeqFocus false

def moves : List (Finset (Fin 4)) := [{0, 1}, {0, 2}, {0, 3}, {0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {0, 1, 2, 3}]

/-- The reward example's 22 linear inequalities together with total mass 111. -/
def Invariant (w : State (Fin 4)) : Prop :=
  w 0 + w 1 + w 2 + w 3 = 111 ∧
  -1 * w 0 + -1 * w 1 + -1 * w 2 ≤ (-677 / 9) ∧
  -1 * w 0 + -1 * w 1 + (-1 / 2) * w 2 ≤ (-172 / 3) ∧
  -1 * w 0 + (-11 / 19) * w 1 + (-15 / 38) * w 2 ≤ (-860 / 19) ∧
  -1 * w 0 + (-1 / 2) * w 1 + (-597 / 38) * w 2 ≤ (-73793 / 171) ∧
  -1 * w 0 + (-19 / 417) * w 1 + (-218 / 417) * w 2 ≤ (-147586 / 3753) ∧
  -1 * w 0 + (-5073 / 119791) * w 1 + (-5365 / 17113) * w 2 ≤ (-3806230 / 119791) ∧
  -1 * w 0 + (-19 / 616) * w 1 + (-1 / 2) * w 2 ≤ (-141259 / 3696) ∧
  -1 * w 1 + (-199 / 19) * w 2 ≤ (-147586 / 513) ∧
  -1 * w 1 + -2 * w 2 ≤ (-677 / 9) ∧
  -1 * w 1 ≤ (-11 / 3) ∧
  -1 * w 2 ≤ (-445 / 18) ∧
  1 * w 2 ≤ 100 ∧
  1 * w 1 ≤ (221 / 6) ∧
  1 * w 1 + (161 / 379) * w 2 ≤ (19890 / 379) ∧
  1 * w 0 + -1 * w 1 + (-289 / 19) * w 2 ≤ (-128605 / 342) ∧
  1 * w 0 + -1 * w 1 + 1 * w 2 ≤ 100 ∧
  1 * w 0 + (-1 / 4) * w 1 + -1 * w 2 ≤ (-11 / 12) ∧
  1 * w 0 + (-57 / 488) * w 1 + (-109 / 122) * w 2 ≤ (7459 / 1464) ∧
  1 * w 0 + (-109 / 1464) * w 1 + (-623 / 732) * w 2 ≤ (2725 / 366) ∧
  1 * w 0 + (1 / 5) * w 1 + (-3 / 5) * w 2 ≤ (221 / 10) ∧
  1 * w 0 + 1 * w 1 + -1 * w 2 ≤ (221 / 6) ∧
  1 * w 0 + 1 * w 1 + 1 * w 2 ≤ (221 / 2)

set_option maxHeartbeats 2000000 in
/-- Every listed nontrivial star move preserves all constraints of the reward invariant. -/
theorem average_mem (w : State (Fin 4)) (hw : Invariant w)
    (S : Finset (Fin 4)) (hS : S ∈ moves) : Invariant (average S w) := by
  rcases hw with ⟨hm, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21⟩
  simp only [moves, List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold Invariant
  all_goals (repeat' apply And.intro)
  all_goals norm_num [average, mean, Finset.sum_insert,
    Finset.card_insert_of_notMem, Fin.ext_iff] <;> linarith

/-- Every state in the invariant has linear reward at most 20361/5. -/
theorem objective_le (w : State (Fin 4)) (hw : Invariant w) :
    (1 / 10) * w 0 + 100 * w 1 + 10 * w 2 + w 3 ≤ 20361 / 5 := by
  rcases hw with ⟨hm, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21⟩
  linarith only [hm, h6, h12, h13]

end WaterTransport.RewardCertificate
