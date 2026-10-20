import WaterTransport1.S05_MinimalLength
import Mathlib.Combinatorics.SimpleGraph.Star
import Mathlib.Data.List.Sort
import Mathlib.Algebra.Order.Field.Power

/-!
# Paper 1, Theorem 4.1: optimal transport to a star's center

`star n` has center 0 and `n` leaves. The explicit strategy takes exactly those
leaves whose initial level exceeds the center's initial level, orders them by
nondecreasing initial level, and averages each leaf with the center in turn.
Equal initial levels may be ordered arbitrarily.

Proof route: a reverse-mass invariant; summation by parts; evaluation of the
greedy strategy; global optimality and the length bound.
-/

/-!
## Preparation: a reverse-mass invariant for arbitrary strategies

Starting at unit mass on the center, any `k` leaves carry at most `1 - 2^(-k)`.
The invariant covers repeated moves and averages involving several leaves.
Summation by parts converts it to a global bound attained by the greedy strategy.
This proof uses finite sums and strategies independently of general attainment.
-/

namespace WaterTransport.StarInvariant

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every vertex set omitting the center satisfies the geometric mass bound. -/
private def Holds (c : V) (p : State V) : Prop :=
  Nonnegative p ∧ mass p = 1 ∧
    ∀ A : Finset V, c ∉ A → ∑ v ∈ A, p v ≤ 1 - (1 / 2 : ℝ) ^ A.card

private theorem initial (c : V) : Holds c (pointMass c) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v; simp only [pointMass]; split_ifs <;> norm_num
  · simp [mass, pointMass]
  · intro A hc
    have hz : ∑ v ∈ A, pointMass c v = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      simp [pointMass, show v ≠ c from fun h => hc (h ▸ hv)]
    rw [hz]
    exact sub_nonneg.mpr (pow_le_one₀ (by norm_num) (by norm_num))

private theorem card_geometric (k : ℕ) :
    (k + 1 : ℝ) * (1 / 2 : ℝ)^k ≤ 1 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ]
    push_cast
    nlinarith [pow_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) k,
      mul_nonneg (Nat.cast_nonneg k) (pow_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) k)]

private theorem fraction_le (s m : ℕ) (h : s + 1 ≤ m) :
    (s : ℝ) / m ≤ 1 - (1 / 2 : ℝ)^s := by
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hsm : (s : ℝ) + 1 ≤ m := by exact_mod_cast h
  have hq := card_geometric s
  have hp : (1 / 2 : ℝ)^s ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  apply (div_le_iff₀ hm).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hsm) (sub_nonneg.mpr hp)]

/-- Any complete average containing the center preserves the invariant. -/
private theorem average (c : V) (p : State V) (hp : Holds c p) (S : Finset V) (hc : c ∈ S) :
    Holds c (WaterTransport.average S p) := by
  refine ⟨average_nonnegative S hp.1, (average_mass S p).trans hp.2.1, ?_⟩
  intro A hA
  let R := A \ S
  let T := A ∩ S
  let r : ℝ := ∑ v ∈ R, p v
  let α : ℝ := (T.card : ℝ) / S.card
  have hScard : (0 : ℝ) < S.card := Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨c, hc⟩)
  have hdis : Disjoint R S := Finset.disjoint_left.mpr
    (fun v hv hs => (Finset.mem_sdiff.mp hv).2 hs)
  have hmass : r + (∑ v ∈ S, p v) ≤ 1 := by
    rw [← hp.2.1]
    change (∑ v ∈ R, p v) + (∑ v ∈ S, p v) ≤ ∑ v, p v
    rw [← Finset.sum_union hdis]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun v _ _ => hp.1 v)
  have hR : r ≤ 1 - (1 / 2 : ℝ)^R.card :=
    hp.2.2 R (fun h => hA (Finset.mem_sdiff.mp h).1)
  have hcard : T.card + 1 ≤ S.card := by
    have hsub : insert c T ⊆ S := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact hc
      · exact (Finset.mem_inter.mp hv).2
    have hnot : c ∉ T := fun h => hA (Finset.mem_inter.mp h).1
    simpa only [Finset.card_insert_of_notMem hnot] using Finset.card_le_card hsub
  have hα : α ≤ 1 - (1 / 2 : ℝ)^T.card := fraction_le _ _ hcard
  have hα0 : 0 ≤ α := div_nonneg (Nat.cast_nonneg _) hScard.le
  have hα1 : α ≤ 1 := hα.trans (sub_le_self _ (pow_nonneg (by norm_num) _))
  have hsum : ∑ v ∈ A, WaterTransport.average S p v =
      r + α * (∑ v ∈ S, p v) := by
    rw [← Finset.sum_inter_add_sum_sdiff A S]
    have hi : ∑ v ∈ A ∩ S, WaterTransport.average S p v = T.card * mean S p := by
      calc
        _ = ∑ _v ∈ T, mean S p :=
          Finset.sum_congr rfl (fun v hv => average_apply_mem S p (Finset.mem_inter.mp hv).2)
        _ = _ := by simp
    have hr : ∑ v ∈ A \ S, WaterTransport.average S p v = r :=
      Finset.sum_congr rfl (fun v hv => average_apply_not_mem S p (Finset.mem_sdiff.mp hv).2)
    rw [hi, hr]
    dsimp [α, mean]
    ring
  have hcount : A.card = R.card + T.card := by
    simpa only [add_comm] using (Finset.card_inter_add_card_sdiff A S).symm
  rw [hsum, hcount, pow_add]
  have h₁ := mul_le_mul_of_nonneg_left hmass hα0
  have h₂ := mul_le_mul_of_nonneg_left hR (sub_nonneg.mpr hα1)
  have h₃ := mul_le_mul_of_nonneg_left hα (pow_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) R.card)
  nlinarith

/-!
## Preparation: turn subset-mass bounds into a reward bound

Define the successive pair-average value, then compare arbitrary reverse profiles by summation by parts.
-/

/-- The center value obtained by successive pair averages with the listed leaves. -/
private noncomputable def value (w : State V) : ℝ → List V → ℝ
  | a, [] => a
  | a, v :: L => value w ((a + w v) / 2) L

omit [Fintype V] [DecidableEq V] in
private theorem value_sub (w : State V) (L : List V) (a b : ℝ) :
    value w a L - value w b L = (a - b) * (1 / 2 : ℝ)^L.length := by
  induction L generalizing a b with
  | nil => simp [value]
  | cons v L ih =>
    rw [value, value, ih, List.length_cons, pow_succ]
    ring

/-- Summation by parts: tail-mass bounds control a weighted sum with ordered weights. -/
private theorem weighted_le (p w : State V) (L : List V) (hd : L.Nodup)
    (hs : L.Pairwise (fun u v => w u ≤ w v)) (a : ℝ) (ha : ∀ v ∈ L, a ≤ w v)
    (hc : ∀ A : Finset V, A ⊆ L.toFinset →
      ∑ v ∈ A, p v ≤ 1 - (1 / 2 : ℝ)^A.card) :
    ∑ v ∈ L.toFinset, (w v - a) * p v ≤ value w a L - a := by
  induction L generalizing a with
  | nil => simp [value]
  | cons v L ih =>
    obtain ⟨hv, hd⟩ := List.nodup_cons.mp hd
    obtain ⟨hvl, hs⟩ := List.pairwise_cons.mp hs
    have hcL : ∀ A : Finset V, A ⊆ L.toFinset →
        ∑ u ∈ A, p u ≤ 1 - (1 / 2 : ℝ)^A.card := by
      intro A hA
      exact hc A (hA.trans (by simp only [List.toFinset_cons]; exact Finset.subset_insert _ _))
    have htail := ih hd hs (w v) hvl hcL
    have hmass := hc (v :: L).toFinset (Finset.Subset.refl _)
    have hn : (v :: L).toFinset.card = L.length + 1 := by
      rw [List.toFinset_card_of_nodup (List.nodup_cons.mpr ⟨hv, hd⟩), List.length_cons]
    rw [hn, pow_succ] at hmass
    have hhead := mul_le_mul_of_nonneg_left hmass
      (sub_nonneg.mpr (ha v (List.mem_cons_self ..)))
    have hsum : ∑ u ∈ (v :: L).toFinset, (w u - a) * p u =
        (w v - a) * (∑ u ∈ (v :: L).toFinset, p u) +
          ∑ u ∈ L.toFinset, (w u - w v) * p u := by
      have hv' : v ∉ L.toFinset := by simpa using hv
      simp only [List.toFinset_cons, Finset.sum_insert hv', sub_mul,
        Finset.sum_sub_distrib, ← Finset.mul_sum]
      ring
    rw [hsum, value]
    have hdiff := value_sub w L ((a + w v) / 2) (w v)
    nlinarith

/-- Only leaves initially above the center contribute positively to the target improvement. -/
private theorem pairing_le (c : V) (p w : State V) (hp : Holds c p) (L : List V)
    (hd : L.Nodup) (hm : ∀ v, v ∈ L ↔ v ≠ c ∧ w c < w v)
    (hs : L.Pairwise (fun u v => w u ≤ w v)) :
    pairing p w ≤ value w (w c) L := by
  have hc : ∀ A : Finset V, A ⊆ L.toFinset →
      ∑ v ∈ A, p v ≤ 1 - (1 / 2 : ℝ)^A.card := by
    intro A hA
    apply hp.2.2 A
    intro hc
    exact ((hm c).mp (List.mem_toFinset.mp (hA hc))).1 rfl
  have hbound := weighted_le p w L hd hs (w c)
    (fun v hv => ((hm v).mp hv).2.le) hc
  have hnonpos : ∑ v ∈ Finset.univ \ L.toFinset, (w v - w c) * p v ≤ 0 := by
    apply Finset.sum_nonpos
    intro v hv
    apply mul_nonpos_of_nonpos_of_nonneg _ (hp.1 v)
    apply sub_nonpos.mpr
    by_contra h
    have hgt := lt_of_not_ge h
    have hvc : v ≠ c := fun hvc => (ne_of_lt hgt) (congrArg w hvc.symm)
    exact (Finset.mem_sdiff.mp hv).2 (List.mem_toFinset.mpr ((hm v).mpr ⟨hvc, hgt⟩))
  have hsplit := Finset.sum_sdiff (f := fun v => (w v - w c) * p v)
    (Finset.subset_univ L.toFinset)
  have hlin : pairing p w = w c + ∑ v, (w v - w c) * p v := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    change pairing p w = w c + ((∑ v, w v * p v) - w c * mass p)
    rw [hp.2.1, mul_one]
    simp only [pairing, mul_comm]
    ring
  rw [hlin]
  linarith

omit [Fintype V] [DecidableEq V] in
private theorem value_congr (w u : State V) (a : ℝ) (L : List V)
    (h : ∀ v ∈ L, w v = u v) : value w a L = value u a L := by
  induction L generalizing a with
  | nil => rfl
  | cons v L ih =>
    rw [value, value, h v (List.mem_cons_self ..)]
    exact ih _ (fun z hz => h z (List.mem_cons_of_mem _ hz))

/-- With no repeated leaf, each leaf still has its initial level when it is first visited. -/
private theorem run_value (c : V) (w : State V) (L : List V)
    (hd : L.Nodup) (hc : c ∉ L) :
    run (L.map fun v => ({c, v} : Finset V)) w c = value w (w c) L := by
  induction L generalizing w with
  | nil => rfl
  | cons v L ih =>
    have hv : v ≠ c := by intro h; exact hc (by simp [h])
    have hvc : c ≠ v := hv.symm
    have hcL : c ∉ L := fun h => hc (List.mem_cons_of_mem _ h)
    obtain ⟨hvL, hdL⟩ := List.nodup_cons.mp hd
    simp only [List.map_cons, run_cons]
    rw [ih _ hdL hcL]
    have hcenter : WaterTransport.average {c, v} w c = (w c + w v) / 2 := by
      simp [WaterTransport.average, mean, hvc, Finset.sum_insert,
        Finset.card_insert_of_notMem]
    rw [hcenter, value]
    apply value_congr
    intro z hz
    apply average_apply_not_mem
    intro hzS
    rcases Finset.mem_insert.mp hzS with rfl | hzS
    · exact hcL hz
    · have hzv := Finset.mem_singleton.mp hzS
      exact hvL (hzv ▸ hz)

end WaterTransport.StarInvariant

namespace WaterTransport

/-!
## Definitions: the star and its greedy leaf order

List precisely the leaves above the initial center level and sort their initial levels.
-/

def star (n : ℕ) : SimpleGraph (Fin (n + 1)) := SimpleGraph.starGraph 0

/-- Each required leaf appears exactly once, in nondecreasing order of initial level. -/
def IsGreedyLeafOrder {n : ℕ} (w : State (Fin (n + 1))) (L : List (Fin (n + 1))) : Prop :=
  L.Nodup ∧ (∀ v, v ∈ L ↔ v ≠ 0 ∧ w 0 < w v) ∧
    L.Pairwise (fun u v => w u ≤ w v)

/-- Average each listed leaf with the center; these pairs are connected in the star. -/
def starGreedyStrategy {n : ℕ} (L : List (Fin (n + 1))) : Strategy (Fin (n + 1)) :=
  L.map fun v => {0, v}

theorem exists_greedyLeafOrder {n : ℕ} (w : State (Fin (n + 1))) :
    ∃ L, IsGreedyLeafOrder w L := by
  classical
  let r : Fin (n + 1) → Fin (n + 1) → Prop := fun u v => w u ≤ w v
  letI : IsTrans (Fin (n + 1)) r := ⟨fun _ _ _ => le_trans⟩
  letI : Std.Total r := ⟨fun u v => le_total (w u) (w v)⟩
  let s := Finset.univ.filter (fun v : Fin (n + 1) => v ≠ 0 ∧ w 0 < w v)
  let L := s.toList.mergeSort (fun u v => decide (r u v))
  have hp := List.mergeSort_perm s.toList (fun u v => decide (r u v))
  refine ⟨L, hp.nodup_iff.mpr s.nodup_toList, ?_, List.pairwise_mergeSort' r s.toList⟩
  intro v
  rw [hp.mem_iff]
  simp [s]

/-- A connected selected set omitting the center of a star must be a singleton. -/
private theorem star_legal_center_or_singleton {n : ℕ} (S : Finset (Fin (n + 1)))
    (hS : IsLegalMove (star n) S) : 0 ∈ S ∨ ∃ v, S = {v} := by
  by_cases hc : 0 ∈ S
  · exact Or.inl hc
  · right
    obtain ⟨v, hv⟩ := hS.1
    have hn : ∀ a b : (S : Set (Fin (n + 1))),
        ¬ ((star n).induce (S : Set (Fin (n + 1)))).Adj a b := by
      intro a b hab
      change a.val ≠ b.val ∧ (a.val = 0 ∨ b.val = 0) at hab
      rcases hab.2 with h | h
      · exact hc (h ▸ a.property)
      · exact hc (h ▸ b.property)
    refine ⟨v, Finset.ext (fun u => ?_)⟩
    simp only [Finset.mem_singleton]
    constructor
    · intro hu
      obtain ⟨p⟩ := hS.2.preconnected ⟨u, hu⟩ ⟨v, hv⟩
      cases p with
      | nil => rfl
      | cons hadj _ => exact (hn _ _ hadj).elim
    · rintro rfl; exact hv

/-!
## Main conclusions: the greedy algorithm and Theorem 4.1

Evaluate the explicit strategy and show that its value attains the global reverse-profile bound.
-/

/-- Section 4's explicit algorithm: legality, global optimality, and a length bound.
The reverse-mass estimate compares against strategies of every finite length. -/
theorem starGreedyStrategy_optimal {n : ℕ} (w : State (Fin (n + 1))) (hw : Nonnegative w)
    (L : List (Fin (n + 1))) (hL : IsGreedyLeafOrder w L) :
    IsOptimal (star n) w 0 (starGreedyStrategy L) ∧ (starGreedyStrategy L).length ≤ n := by
  clear hw -- The comparison also permits real input; the public statement retains the paper's nonnegativity assumption.
  have hc : (0 : Fin (n + 1)) ∉ L := fun h => ((hL.2.1 0).mp h).1 rfl
  have hlegal : IsLegal (star n) (starGreedyStrategy L) := by
    intro S hS
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hS
    have hv0 : v ≠ 0 := ((hL.2.1 v).mp hv).1
    refine ⟨⟨0, by simp⟩, ?_⟩
    have hadj : (star n).Adj 0 v := by
      change 0 ≠ v ∧ ((0 : Fin (n + 1)) = 0 ∨ v = 0)
      exact ⟨hv0.symm, Or.inl rfl⟩
    have he : (({0, v} : Finset (Fin (n + 1))) : Set (Fin (n + 1))) = {0, v} := by
      ext z
      simp
    rw [he]
    exact SimpleGraph.induce_pair_connected_of_adj hadj
  have hrun : ∀ σ : Strategy (Fin (n + 1)), IsLegal (star n) σ →
      ∀ p, StarInvariant.Holds 0 p → StarInvariant.Holds 0 (run σ p) := by
    intro σ
    induction σ with
    | nil => intro _ p hp; exact hp
    | cons S σ ih =>
      intro hσ p hp
      obtain ⟨hS, hσ⟩ := (isLegal_cons _ _ _).mp hσ
      apply ih hσ
      rcases star_legal_center_or_singleton S hS with hS | ⟨v, rfl⟩
      · exact StarInvariant.average 0 p hp S hS
      · simpa only [average_singleton] using hp
  constructor
  · refine ⟨hlegal, ?_⟩
    intro σ hσ
    change run σ w 0 ≤ run (starGreedyStrategy L) w 0
    rw [reverseProfile_duality]
    change pairing (reverseProfile σ 0) w ≤ run (L.map fun v => {0, v}) w 0
    rw [StarInvariant.run_value 0 w L hL.1 hc]
    apply StarInvariant.pairing_le 0 _ w _ L hL.1 hL.2.1 hL.2.2
    exact hrun σ.reverse (fun S hS => hσ S (List.mem_reverse.mp hS)) _
      (StarInvariant.initial 0)
  · have hsub : L.toFinset ⊆ Finset.univ.erase (0 : Fin (n + 1)) := by
      intro v hv
      exact Finset.mem_erase.mpr ⟨((hL.2.1 v).mp (List.mem_toFinset.mp hv)).1,
        Finset.mem_univ v⟩
    have hcard := Finset.card_le_card hsub
    simpa only [starGreedyStrategy, List.length_map, List.toFinset_card_of_nodup hL.1,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
      Nat.add_sub_cancel] using hcard

/-- Theorem 4.1: at most `n` moves suffice. For `n = 0`, doing nothing is optimal. -/
theorem star_optimalLength_le (n : ℕ) (w : State (Fin (n + 1))) (hw : Nonnegative w) :
    optimalLength (star n) w hw 0 ≤ n := by
  obtain ⟨L, hL⟩ := exists_greedyLeafOrder w
  obtain ⟨hopt, hlen⟩ := starGreedyStrategy_optimal w hw L hL
  exact (optimalLength_le (star n) w hw 0 _ hopt).trans hlen

end WaterTransport
