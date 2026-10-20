import WaterTransport1.S08_PathTheorem
import WaterTransport1.S10_FiniteCertificates
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Paper 1, Section 4: Examples 4.1 and 4.2

Each example specifies its graph, initial weights, target, and witness.
All numerical calculations use exact arithmetic. The paper's vertices
v_1,...,v_9 correspond to Lean indices 0,...,8.

Reading order: Example 4.1 (two path moves are necessary); Example 4.2 (more than
three moves on a spider). Finite-horizon bounds use the sound rational checkers
in S10_FiniteCertificates. Example 4.3 is outside the current project scope.
-/

namespace WaterTransport
namespace Examples

set_option maxRecDepth 1024

/-!
## Example 4.1: two moves are necessary, and the first lowers the target

Define the five-vertex input and witness, evaluate it exactly, bound all one-step
and two-step competitors, then use the path theorem for global optimality.
-/

def pathWeights : State (Fin 5) := fun v =>
  match v.val with
  | 3 => 0
  | 4 => 15
  | _ => 4

def pathWitness : Strategy (Fin 5) := [{0, 1, 2, 3}, {2, 3, 4}]

private theorem pathWeights_nonnegative : Nonnegative pathWeights := by
  intro v
  fin_cases v <;> norm_num [pathWeights]

private theorem pathWitness_legal : IsLegal (SimpleGraph.pathGraph 5) pathWitness := by
  intro S hS
  simp only [pathWitness, List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl
  · convert pathInterval_legal (0 : Fin 5) 3 (by decide) using 1; decide
  · convert pathInterval_legal (2 : Fin 5) 4 (by decide) using 1; decide

private def pathWeightsQ : Fin 5 → ℚ := fun v =>
  match v.val with
  | 3 => 0
  | 4 => 15
  | _ => 4

private theorem pathWeights_cast : pathWeights = fun v => (pathWeightsQ v : ℝ) := by
  funext v
  fin_cases v <;> norm_num [pathWeights, pathWeightsQ]

theorem pathWitness_value : run pathWitness pathWeights 2 = 7 := by
  rw [pathWeights_cast, runQ_cast]
  change (runQ pathWitness pathWeightsQ 2 : ℝ) = 7
  rw [show runQ pathWitness pathWeightsQ 2 = 7 by decide +kernel]
  norm_num

/-- The target starts at 4, falls to 3 after the first move, and reaches 7 after the second. -/
theorem pathWitness_first_decreases : average ({0, 1, 2, 3} : Finset (Fin 5)) pathWeights 2 = 3 := by
  norm_num [pathWeights, average, mean, Finset.sum_insert,
    Finset.card_insert_of_notMem, Fin.ext_iff]

private theorem mean_path_formula (a b : Fin 5) (u : State (Fin 5)) :
    mean (pathInterval a b) u =
      (∑ v : Fin 5, if a ≤ v ∧ v ≤ b then u v else 0) / (b.val + 1 - a.val : ℕ) := by
  have he : pathInterval a b = Finset.univ.filter (fun v => a ≤ v ∧ v ≤ b) := by
    ext v
    simp [pathInterval]
  unfold mean
  rw [show (pathInterval a b).card = b.val + 1 - a.val from Fin.card_Icc a b]
  rw [he, Finset.sum_filter]

private theorem path_one_interval_bound (a b : Fin 5) (hab : a ≤ b) :
    average (pathInterval a b) pathWeights 2 ≤ 19 / 3 := by
  simp only [average, mean_path_formula]
  fin_cases a <;> fin_cases b <;>
    simp only [pathInterval, Finset.mem_Icc, Fin.sum_univ_succ, Fin.le_def] at hab ⊢ <;>
    norm_num [pathWeights] at *

private theorem path_one_step_max : horizonMax (SimpleGraph.pathGraph 5) pathWeights 2 1 = 19 / 3 := by
  apply le_antisymm
  · apply horizonMax_le
    intro σ hσ hlen
    cases σ with
    | nil => norm_num [run, pathWeights]
    | cons S σ =>
      have hnil : σ = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst σ
      obtain ⟨a, b, hab, rfl⟩ := (path_legal_iff_interval S).mp ((isLegal_cons _ _ _).mp hσ).1
      exact path_one_interval_bound a b hab
  · have hleg : IsLegal (SimpleGraph.pathGraph 5) [{2, 3, 4}] := by
      simpa only [isLegal_cons, isLegal_nil, and_true] using
        (show IsLegalMove (SimpleGraph.pathGraph 5) {2, 3, 4} from by
          convert pathInterval_legal (2 : Fin 5) 4 (by decide) using 1; decide)
    have hv : run [{2, 3, 4}] pathWeights 2 = 19 / 3 := by
      norm_num [run, average, mean, pathWeights, Finset.sum_insert,
        Finset.card_insert_of_notMem, Fin.ext_iff]
    rw [← hv]
    exact le_horizonMax _ _ _ _ _ hleg (by decide)

private def pathMoves : List (Finset (Fin 5)) :=
  (List.finRange 5).flatMap (fun a => (List.finRange 5).map (pathInterval a))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem path_two_certificate : checkBound pathMoves (fun w => w 2) 7 2 pathWeightsQ = true := by
  decide +kernel

/-- The two-step certificate and the path theorem make 7 the maximum over all finite strategies. -/
theorem path_optimum : targetSup (SimpleGraph.pathGraph 5) pathWeights 2 = 7 := by
  rw [path_targetSup_eq_horizon_two pathWeights pathWeights_nonnegative]
  apply le_antisymm
  · apply horizonMax_le
    intro σ hσ hlen
    rw [pathWeights_cast, runQ_cast]
    have hb := checkBound_sound pathMoves (fun w => w 2) 7 2 pathWeightsQ
      path_two_certificate σ (fun S hS => ?_) hlen
    · change (runQ σ pathWeightsQ 2 : ℝ) ≤ 7
      exact_mod_cast hb
    obtain ⟨a, b, _, rfl⟩ := (path_legal_iff_interval S).mp (hσ S hS)
    apply List.mem_flatMap.mpr
    exact ⟨a, by simp, List.mem_map.mpr ⟨b, by simp, rfl⟩⟩
  · rw [← pathWitness_value]
    exact le_horizonMax _ _ _ _ _ pathWitness_legal (by decide)

theorem path_two_steps_necessary :
    optimalLength (SimpleGraph.pathGraph 5) pathWeights pathWeights_nonnegative 2 = 2 := by
  apply le_antisymm (path_optimalLength_le_two pathWeights pathWeights_nonnegative 2)
  by_contra h
  have hlen : optimalLength (SimpleGraph.pathGraph 5) pathWeights pathWeights_nonnegative 2 ≤ 1 :=
    by omega
  obtain ⟨σ, hσ, hσlen⟩ := (optimalLength_le_iff _ pathWeights pathWeights_nonnegative 2 1).mp hlen
  have hu := le_horizonMax (SimpleGraph.pathGraph 5) pathWeights 2 1 σ hσ.1 hσlen
  have hl : run pathWitness pathWeights 2 ≤ run σ pathWeights 2 := hσ.2 _ pathWitness_legal
  rw [path_one_step_max] at hu
  rw [pathWitness_value] at hl
  linarith

/-!
## Example 4.2: a spider with arm lengths 4, 2, and 2

Figure 6 has edges v_1-v_2-v_3-v_4-v_5, v_1-v_6-v_7, and v_1-v_8-v_9.
A four-step witness beats every strategy of length at most three. The conclusion
is a strict lower bound on the shortest optimal length; witness optimality is not asserted.
-/


noncomputable def spiderWeights : State (Fin 9) := fun v =>
  if v = 0 then 101 / 10 else
  if v = 1 then 10 else
  if v = 2 then 0 else
  if v = 3 then 100 else
  if v = 4 then 10000 else
  if v = 5 then 98 / 10 else
  if v = 6 then 1000 else
  if v = 7 then 101 / 10 else 9

def spiderWitness : Strategy (Fin 9) :=
  [{0, 5, 7}, {0, 1, 2, 7, 8}, {0, 1, 2, 3, 5, 6}, {0, 1, 2, 3, 4}]

private theorem spiderWeights_nonnegative : Nonnegative spiderWeights := by
  intro v
  fin_cases v <;> norm_num [spiderWeights, Fin.ext_iff]

private theorem spiderWitness_legal : IsLegal spiderGraph spiderWitness := by
  unfold IsLegal IsLegalMove spiderWitness
  decide +kernel

private theorem spiderWeights_cast : spiderWeights = fun v => (spiderWeightsQ v : ℝ) := by
  funext v
  fin_cases v <;> norm_num [spiderWeights, spiderWeightsQ, Fin.ext_iff]

theorem spiderWitness_value : run spiderWitness spiderWeights 0 = 53778 / 25 := by
  rw [spiderWeights_cast, runQ_cast]
  change (runQ spiderWitness spiderWeightsQ 0 : ℝ) = 53778 / 25
  rw [show runQ spiderWitness spiderWeightsQ 0 = 53778 / 25 by decide +kernel]
  norm_num


/-- The universal upper bound for strategies of length at most three, checked exactly. -/
private theorem spider_three_step_max : horizonMax spiderGraph spiderWeights 0 3 = 806666 / 375 := by
  apply le_antisymm
  · apply horizonMax_le
    intro σ hσ hlen
    let τ := σ.filter (fun S => 2 ≤ S.card)
    have hm : ∀ S ∈ τ, S ∈ spiderMoves := by
      intro S hS
      have hs := List.mem_filter.mp hS
      exact spider_moves_complete S (hσ S hs.1) (of_decide_eq_true hs.2)
    have hb := checkCoordinateBound_sound spiderMoves 0 (806666 / 375) 3 (Vector.ofFn spiderWeightsQ)
      spider_three_certificate τ hm ((List.length_filter_le _ _).trans hlen)
    simp only [Vector.getElem_ofFn, Fin.eta] at hb
    rw [← run_filter_nontrivial σ spiderWeights, spiderWeights_cast, runQ_cast]
    change (runQ τ spiderWeightsQ 0 : ℝ) ≤ 806666 / 375
    have hc : (runQ τ spiderWeightsQ 0 : ℝ) ≤ ((806666 / 375 : ℚ) : ℝ) :=
      Rat.cast_le.mpr hb
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at hc
    exact hc
  · let τ : Strategy (Fin 9) :=
      [{0, 1, 2, 7, 8}, {0, 1, 2, 3, 5, 6}, {0, 1, 2, 3, 4}]
    have hτ : IsLegal spiderGraph τ := by
      intro S hS
      apply spiderWitness_legal S
      simp only [τ, List.mem_cons, List.not_mem_nil, or_false] at hS
      simp only [spiderWitness, List.mem_cons, List.not_mem_nil, or_false]
      exact Or.inr hS
    have hvalQ : runQ τ spiderWeightsQ 0 = 806666 / 375 := by decide +kernel
    have hval : run τ spiderWeights 0 = 806666 / 375 := by
      rw [spiderWeights_cast, runQ_cast]
      change (runQ τ spiderWeightsQ 0 : ℝ) = 806666 / 375
      rw [hvalQ]
      norm_num
    rw [← hval]
    exact le_horizonMax _ _ _ _ _ hτ (by decide)

theorem spider_four_steps_beat_three (σ : Strategy (Fin 9))
    (hσ : IsLegal spiderGraph σ) (hlen : σ.length ≤ 3) :
    run σ spiderWeights 0 < run spiderWitness spiderWeights 0 := by
  have h := le_horizonMax spiderGraph spiderWeights 0 3 σ hσ hlen
  rw [spider_three_step_max] at h
  rw [spiderWitness_value]
  linarith

/-- The paper's conclusion: the shortest optimal length is greater than three. -/
theorem spider_optimalLength_gt_three :
    3 < optimalLength spiderGraph spiderWeights spiderWeights_nonnegative 0 := by
  by_contra h
  obtain ⟨σ, hσ, hlen⟩ := (optimalLength_le_iff spiderGraph spiderWeights
    spiderWeights_nonnegative 0 3).mp (le_of_not_gt h)
  exact (not_lt_of_ge (hσ.2 spiderWitness spiderWitness_legal))
    (spider_four_steps_beat_three σ hσ.1 hlen)

end Examples
end WaterTransport
