import WaterTransport3.S03_UniformBound
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Data.List.Sublists

/-!
# Paper 3, Section 7: executable rational exhaustive search

Enumerate all nontrivial legal moves and all strategies of length at most L_n,
then evaluate and compare them in the rationals using Paper 1's `runQ`.
The returned strategy is computed by a finite search.

Reading order: the algorithm; enumeration and maximum-selection lemmas; global
correctness using the uniform bound; exact optimum and threshold decision;
search-tree size. Binary bit complexity and the NEXP classification require a
separate input encoding and machine-time model and are not formalized here.
-/

namespace WaterTransport.Paper3

variable {n : ℕ}

/-!
## Algorithm definitions: enumerate, execute, and select

All comparisons are exact rational comparisons, with a decidable adjacency relation supplied as input.
-/

/-- Enumerate vertex subsets as sublists of `Fin n`, then test nontriviality and
legality. This gives an executable list without noncomputable `Finset.toList`. -/
private def legalMoves (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : List (Finset (Fin n)) :=
  ((List.finRange n).sublists.map List.toFinset).filter fun S => 2 ≤ S.card ∧ S.Nonempty ∧ (G.induce (S : Set (Fin n))).Connected

/-- Include the option to stop at every depth, so this enumerates lengths at most `k`. -/
private def searchWords (moves : List (Finset (Fin n))) : ℕ → List (Strategy (Fin n))
  | 0 => [[]]
  | k + 1 => [[]] ++ moves.flatMap (fun S => (searchWords moves k).map (List.cons S))

private def chooseBetter (w : Fin n → ℚ) (x : Fin n) (σ τ : Strategy (Fin n)) : Strategy (Fin n) :=
  if runQ σ w x ≤ runQ τ w x then τ else σ

/-- Return an explicit maximizing strategy. On a tie, keep the later visited strategy. -/
def exactSearch (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : Fin n → ℚ) (x : Fin n) : Strategy (Fin n) :=
  (searchWords (legalMoves G) (uniformLength (n))).foldl (chooseBetter w x) []

/-- The rational target value attained by the computed strategy. -/
def exactValue (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : Fin n → ℚ) (x : Fin n) : ℚ :=
  runQ (exactSearch G w x) w x

/-!
## Preparation: completeness of enumeration and maximum selection

Characterize the generated moves and words and prove that the fold keeps a maximizing candidate.
-/

private theorem mem_legalMoves (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) : S ∈ legalMoves G ↔ 2 ≤ S.card ∧ IsLegalMove G S := by
  simp only [legalMoves, List.mem_filter, decide_eq_true_eq]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨List.mem_map.mpr ⟨(List.finRange n).filter (fun v => v ∈ S),
      List.mem_sublists.mpr List.filter_sublist, ?_⟩, h⟩
    ext v; simp

private theorem mem_searchWords (moves : List (Finset (Fin n))) (k : ℕ)
    (σ : Strategy (Fin n)) :
    σ ∈ searchWords moves k ↔ σ.length ≤ k ∧ ∀ S ∈ σ, S ∈ moves := by
  induction k generalizing σ with
  | zero => cases σ <;> simp [searchWords]
  | succ k ih =>
    cases σ with
    | nil => simp [searchWords]
    | cons S σ =>
      simp [searchWords, List.mem_flatMap, List.mem_map, ih, and_assoc, and_comm,
        and_left_comm]

private theorem fold_best (w : Fin n → ℚ) (x : Fin n) (words : List (Strategy (Fin n)))
    (base : Strategy (Fin n)) :
    words.foldl (chooseBetter w x) base ∈ base :: words ∧
      ∀ σ ∈ base :: words, runQ σ w x ≤ runQ (words.foldl (chooseBetter w x) base) w x := by
  induction words generalizing base with
  | nil => simp
  | cons σ words ih =>
    obtain ⟨hmem, hmax⟩ := ih (chooseBetter w x base σ)
    have hb : runQ base w x ≤ runQ (chooseBetter w x base σ) w x := by
      unfold chooseBetter; split <;> simp_all
    have hs : runQ σ w x ≤ runQ (chooseBetter w x base σ) w x := by
      unfold chooseBetter; split <;> simp_all [le_of_not_ge]
    have hchosen := hmax _ (List.mem_cons_self ..)
    refine ⟨?_, ?_⟩
    · simp only [List.foldl_cons]
      rcases List.mem_cons.mp hmem with heq | ht
      · rw [heq]; unfold chooseBetter; split <;> simp
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ht)
    · intro τ hτ
      rcases List.mem_cons.mp hτ with rfl | hτ
      · exact hb.trans hchosen
      rcases List.mem_cons.mp hτ with rfl | hτ
      · exact hs.trans hchosen
      · exact hmax τ (List.mem_cons_of_mem _ hτ)

/-!
## Correctness: the finite search is globally optimal

Use the uniform length theorem to reduce all finite legal competitors to the enumerated horizon.
-/

/-- For nonnegative rational input, the returned strategy is legal, has length at most L_n, and is globally optimal in the real model. -/
theorem exactSearch_correct (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Fin n → ℚ) (hw : ∀ v, 0 ≤ w v) (x : Fin n) :
    IsOptimal G (fun v => (w v : ℝ)) x (exactSearch G w x) ∧
      (exactSearch G w x).length ≤ uniformLength (n) := by
  have hn : Nonnegative (fun v => (w v : ℝ)) := by
    intro v; change (0 : ℝ) ≤ (w v : ℝ); exact_mod_cast hw v
  obtain ⟨τ, hτ, hlen⟩ := exists_short_optimal G (fun v => (w v : ℝ)) hn x
  simp only [Fintype.card_fin] at hlen
  let τ' := τ.filter fun S => 2 ≤ S.card
  have hmem : τ' ∈ searchWords (legalMoves G) (uniformLength (n)) := by
    apply (mem_searchWords _ _ _).mpr
    refine ⟨(List.length_filter_le _ _).trans hlen, ?_⟩
    intro S hS
    have hs := List.mem_filter.mp hS
    exact (mem_legalMoves G S).mpr ⟨of_decide_eq_true hs.2, hτ.1 S hs.1⟩
  obtain ⟨hchosen, hmax⟩ := fold_best w x
    (searchWords (legalMoves G) (uniformLength (n))) []
  have hchosen' : exactSearch G w x ∈
      searchWords (legalMoves G) (uniformLength (n)) := by
    rcases List.mem_cons.mp hchosen with hnil | hmem
    · rw [show exactSearch G w x = [] from hnil]
      exact (mem_searchWords _ _ _).mpr ⟨by simp, by simp⟩
    · exact hmem
  have hs := (mem_searchWords _ _ _).mp hchosen'
  refine ⟨⟨fun S hS => ((mem_legalMoves G S).mp (hs.2 S hS)).2, ?_⟩, hs.1⟩
  intro σ hσ
  have hle := hτ.2 σ hσ
  change run σ (fun v => (w v : ℝ)) x ≤ run τ (fun v => (w v : ℝ)) x at hle
  have hbest := hmax τ' (List.mem_cons_of_mem _ hmem)
  have hcast : run τ' (fun v => (w v : ℝ)) x ≤
      run (exactSearch G w x) (fun v => (w v : ℝ)) x := by
    simp only [runQ_cast]
    exact_mod_cast hbest
  rw [run_filter_nontrivial] at hcast
  exact hle.trans hcast

/-- The real target supremum equals the computed rational optimum cast to the reals. -/
theorem rational_optimum (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Fin n → ℚ) (hw : ∀ v, 0 ≤ w v) (x : Fin n) :
    targetSup G (fun v => (w v : ℝ)) x = (exactValue G w x : ℝ) := by
  have hn : Nonnegative (fun v => (w v : ℝ)) := by
    intro v; change (0 : ℝ) ≤ (w v : ℝ); exact_mod_cast hw v
  have h := ((isOptimal_iff_attains G _ hn x _).mp (exactSearch_correct G w hw x).1).2
  rw [exactValue, runQ_cast] at *
  exact h.symm

/-!
## Strict-threshold decision and correctness

Relate the executable Boolean answer to existence of a finite legal strategy exceeding the threshold.
-/

/-- An executable decision procedure for strictly exceeding a rational threshold. -/
def exceedsThreshold (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Fin n → ℚ) (x : Fin n) (threshold : ℚ) : Bool :=
  decide (threshold < exactValue G w x)

/-- The Boolean test succeeds exactly when some finite legal strategy exceeds the rational threshold. -/
theorem exceedsThreshold_correct (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Fin n → ℚ) (hw : ∀ v, 0 ≤ w v) (x : Fin n) (threshold : ℚ) :
    exceedsThreshold G w x threshold = true ↔
      ∃ σ : Strategy (Fin n), IsLegal G σ ∧ (threshold : ℝ) < run σ (fun v => (w v : ℝ)) x := by
  have hopt := (exactSearch_correct G w hw x).1
  simp only [exceedsThreshold, decide_eq_true_eq]
  constructor
  · intro h
    refine ⟨exactSearch G w x, hopt.1, ?_⟩
    rw [runQ_cast]
    change (threshold : ℝ) < (exactValue G w x : ℝ)
    exact_mod_cast h
  · rintro ⟨σ, hσ, hval⟩
    have hle : run σ (fun v => (w v : ℝ)) x ≤
        run (exactSearch G w x) (fun v => (w v : ℝ)) x := hopt.2 σ hσ
    have h := hval.trans_le hle
    rw [runQ_cast] at h
    change (threshold : ℝ) < (exactValue G w x : ℝ) at h
    exact_mod_cast h

/-!
## Search-size bookkeeping

Count generated words and bound the search tree. These statements do not constitute a bit-complexity theorem.
-/

/-- The exact recurrence for search-tree node counts, separate from machine running time. -/
private def searchNodes (moves : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => 1 + moves * searchNodes moves k

private theorem searchWords_length (moves : List (Finset (Fin n))) (k : ℕ) :
    (searchWords moves k).length = searchNodes moves.length k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp [searchWords, List.length_flatMap, ih, searchNodes, Nat.add_comm]

private theorem searchNodes_le (m k : ℕ) : searchNodes m k ≤ (m + 1) ^ (k + 1) := by
  induction k with
  | zero => simp [searchNodes]
  | succ k ih =>
    have hpos : 1 ≤ (m + 1) ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
    simp only [searchNodes, pow_succ] at *
    nlinarith

end WaterTransport.Paper3
