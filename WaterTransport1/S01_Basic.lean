import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Paper 1, Section 2: states and complete averaging

The common model for all three papers is a finite undirected simple graph.
A state is real-valued; `Nonnegative` specifies the physical water-level domain.
A legal move completely averages one nonempty induced connected vertex set.

Reading order: definitions; conservation and bounds; identities for redundant
moves; energy dissipation (Lemma 2.1); self-adjointness and affine compatibility.
The paper's sum of squares is named `energy`, separately from any norm.
-/

namespace WaterTransport

/-!
## Definitions: states, legal moves, and observables

These definitions fix the common mathematical model used throughout all three papers.
-/

/-- A real water level at each vertex; physical input states additionally satisfy `Nonnegative`. -/
abbrev State (V : Type*) := V → ℝ

/-- Every vertex has a nonnegative water level. -/
def Nonnegative {V : Type*} (w : State V) : Prop := ∀ v, 0 ≤ w v

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A nonempty vertex set whose induced subgraph is connected.
Connectivity is required inside the selected set. The explicit nonemptiness
condition also makes the mathematical domain visible in the statement. -/
def IsLegalMove (G : SimpleGraph V) (S : Finset V) : Prop :=
  S.Nonempty ∧ (G.induce (S : Set V)).Connected

/-- The mean water level on a finite set. Its auxiliary value on the empty set is
zero; the empty set is not a legal move. -/
noncomputable def mean (S : Finset V) (w : State V) : ℝ :=
  (∑ v ∈ S, w v) / (S.card : ℝ)

/-- Complete averaging: update all coordinates in `S` simultaneously and fix the rest. -/
noncomputable def average (S : Finset V) (w : State V) : State V :=
  fun v => if v ∈ S then mean S w else w v

/-- Total water mass. -/
noncomputable def mass (w : State V) : ℝ := ∑ v, w v

/-- Definition 2.1: the sum of squared water levels, called energy here. -/
noncomputable def energy (w : State V) : ℝ := ∑ v, (w v) ^ 2

/-- The finite real inner product, used for self-adjointness and reverse profiles. -/
noncomputable def pairing (u w : State V) : ℝ := ∑ v, u v * w v

/-- Identify the mean with mathlib's finite expectation to reuse its algebraic API. -/
private theorem mean_eq_expect (S : Finset V) (w : State V) : mean S w = S.expect w := by
  exact (Finset.expect_eq_sum_div_card S w).symm

/-- The averaging map as a real linear operator. Preservation of nonnegativity is proved below. -/
noncomputable def averageLinear (S : Finset V) : State V →ₗ[ℝ] State V where
  toFun := average S
  map_add' w u := by
    funext v
    by_cases hv : v ∈ S <;> simp [average, mean, hv, Finset.sum_add_distrib, add_div]
  map_smul' a w := by
    funext v
    by_cases hv : v ∈ S <;>
      simp [average, mean, hv, ← Finset.mul_sum, mul_div_assoc]

/-!
## Basic lemmas: evaluation, conservation, and bounds

Compute individual coordinates, then prove preservation of nonnegativity, mass, and bounds.
-/

@[simp] theorem average_apply_mem (S : Finset V) (w : State V) {v : V}
    (hv : v ∈ S) : average S w v = mean S w := by
  simp [average, hv]

@[simp] theorem average_apply_not_mem (S : Finset V) (w : State V) {v : V}
    (hv : v ∉ S) : average S w v = w v := by
  simp [average, hv]

@[simp] theorem average_empty (w : State V) : average ∅ w = w := by
  funext v
  simp [average]

@[simp] theorem average_singleton (v : V) (w : State V) : average {v} w = w := by
  funext u
  by_cases h : u = v <;> simp [average, mean, h]

/-- Averaging preserves nonnegativity on any finite set, without a connectivity assumption. -/
theorem average_nonnegative (S : Finset V) {w : State V} (hw : Nonnegative w) :
    Nonnegative (average S w) := by
  intro v
  by_cases hv : v ∈ S
  · simp only [average, if_pos hv, mean]
    exact div_nonneg (Finset.sum_nonneg fun u _ => hw u) (Nat.cast_nonneg _)
  · simpa [average, hv] using hw v

/-- Cardinality times the mean equals the sum, including for the empty set. -/
theorem card_mul_mean (S : Finset V) (w : State V) :
    (S.card : ℝ) * mean S w = ∑ v ∈ S, w v := by
  by_cases hS : S = ∅
  · simp [hS, mean]
  · have hc : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hS))
    unfold mean
    field_simp

/-- Averaging inside a larger set preserves the sum on that larger set. -/
theorem sum_average_of_subset (S T : Finset V) (h : S ⊆ T) (w : State V) :
    ∑ v ∈ T, average S w v = ∑ v ∈ T, w v := by
  have hinside : ∑ v ∈ S, average S w v = ∑ v ∈ S, w v := by
    calc
      _ = ∑ _v ∈ S, mean S w := Finset.sum_congr rfl (fun v hv => average_apply_mem S w hv)
      _ = _ := by simpa using card_mul_mean S w
  calc
    _ = (∑ v ∈ T \ S, average S w v) + ∑ v ∈ S, average S w v :=
      (Finset.sum_sdiff h).symm
    _ = (∑ v ∈ T \ S, w v) + ∑ v ∈ S, w v := by
      rw [hinside]
      congr 1
      exact Finset.sum_congr rfl (fun v hv => average_apply_not_mem S w (Finset.mem_sdiff.mp hv).2)
    _ = _ := Finset.sum_sdiff h

/-- Total mass is preserved, including by the auxiliary empty-set operation. -/
theorem average_mass (S : Finset V) (w : State V) : mass (average S w) = mass w := by
  exact sum_average_of_subset S Finset.univ (Finset.subset_univ S) w

/-- Uniform lower and upper bounds are preserved. This later bounds reachable states in a compact box. -/
theorem average_bounds (S : Finset V) (w : State V) (a b : ℝ)
    (h : ∀ v, a ≤ w v ∧ w v ≤ b) :
    ∀ v, a ≤ average S w v ∧ average S w v ≤ b := by
  intro v
  by_cases hv : v ∈ S
  · rw [average_apply_mem S w hv, mean_eq_expect]
    exact ⟨Finset.le_expect ⟨v, hv⟩ (fun u _ => (h u).1),
      Finset.expect_le ⟨v, hv⟩ (fun u _ => (h u).2)⟩
  · simpa only [average_apply_not_mem S w hv] using h v

/-!
## Preparation for shortening: redundant and independent moves

Idempotence, commutation, and absorption justify deleting or rearranging selected moves.
-/

/-- Two consecutive averages on the same set equal a single average. -/
theorem average_idempotent (S : Finset V) (w : State V) :
    average S (average S w) = average S w := by
  funext v
  by_cases hv : v ∈ S
  · rw [average_apply_mem S _ hv, average_apply_mem S w hv, mean_eq_expect S (average S w)]
    exact (Finset.expect_congr rfl (fun u hu => average_apply_mem S w hu)).trans
      (Finset.expect_const ⟨v, hv⟩ _)
  · exact average_apply_not_mem S _ hv

/-- Disjoint averages commute. This permits rearranging independent moves in Section 3. -/
theorem average_comm_of_disjoint (S T : Finset V) (h : Disjoint S T) (w : State V) :
    average S (average T w) = average T (average S w) := by
  have hST : ∀ v ∈ S, v ∉ T := Finset.disjoint_left.mp h
  have hTS : ∀ v ∈ T, v ∉ S := Finset.disjoint_left.mp h.symm
  have hmS : mean S (average T w) = mean S w := by
    unfold mean
    congr 1
    exact Finset.sum_congr rfl (fun v hv => average_apply_not_mem T w (hST v hv))
  have hmT : mean T (average S w) = mean T w := by
    unfold mean
    congr 1
    exact Finset.sum_congr rfl (fun v hv => average_apply_not_mem S w (hTS v hv))
  funext v
  by_cases hS : v ∈ S
  · simp [average, hS, hST v hS, hmS]
  · by_cases hT : v ∈ T <;> simp [average, hS, hT, hmT]

/-- An average on a subset can be deleted if the larger set is averaged immediately afterwards. -/
theorem average_absorb_subset (S T : Finset V) (h : S ⊆ T) (w : State V) :
    average T (average S w) = average T w := by
  have hm : mean T (average S w) = mean T w := by
    unfold mean
    rw [sum_average_of_subset S T h w]
  funext v
  by_cases hv : v ∈ T
  · simp only [average_apply_mem T _ hv, hm]
  · have hvS : v ∉ S := fun hs => hv (h hs)
    simp only [average_apply_not_mem T _ hv, average_apply_not_mem S _ hvS]

/-- Averaging a subset immediately after its containing set has no further effect. -/
theorem average_subset_absorb (S T : Finset V) (h : S ⊆ T) (w : State V) :
    average S (average T w) = average T w := by
  funext v
  by_cases hv : v ∈ S
  · rw [average_apply_mem S _ hv, average_apply_mem T w (h hv), mean_eq_expect]
    exact (Finset.expect_congr rfl (fun u hu => average_apply_mem T w (h hu))).trans
      (Finset.expect_const ⟨v, hv⟩ _)
  · exact average_apply_not_mem S _ hv

/-!
## Lemma 2.1: energy dissipation and equality

The variance identity gives monotonicity and detects exactly when an operation changes the state.
-/

/-- Exact energy loss equals the sum of squared deviations on the averaged set.
This gives both monotonicity and the equality criterion in Lemma 2.1. -/
theorem energy_drop (S : Finset V) (w : State V) :
    energy w - energy (average S w) = ∑ v ∈ S, (w v - mean S w) ^ 2 := by
  have hout : ∑ v, ((w v)^2 - (average S w v)^2) =
      ∑ v ∈ S, ((w v)^2 - (average S w v)^2) := by
    apply (Finset.sum_subset (Finset.subset_univ S) ?_).symm
    intro v _ hv
    rw [average_apply_not_mem S w hv, sub_self]
  have hmean := card_mul_mean S w
  have hvar : ∑ v ∈ S, (w v - mean S w)^2 =
      (∑ v ∈ S, (w v)^2) - 2 * mean S w * (∑ v ∈ S, w v) +
        (S.card : ℝ) * (mean S w)^2 := by
    calc
      _ = ∑ v ∈ S, ((w v)^2 - (2 * mean S w) * w v + (mean S w)^2) := by
        apply Finset.sum_congr rfl
        intro v _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          Finset.sum_const, nsmul_eq_mul]
  rw [energy, energy, ← Finset.sum_sub_distrib, hout]
  calc
    _ = ∑ v ∈ S, ((w v)^2 - (mean S w)^2) :=
      Finset.sum_congr rfl (fun v hv => by rw [average_apply_mem S w hv])
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hvar, ← hmean]
      ring

/-- Lemma 2.1: averaging decreases energy, for every real state. -/
theorem energy_average_le (S : Finset V) (w : State V) :
    energy (average S w) ≤ energy w := by
  have h := Finset.sum_nonneg (fun v (_ : v ∈ S) => sq_nonneg (w v - mean S w))
  rw [← energy_drop] at h
  linarith

/-- Equality in the energy inequality holds exactly when the state is unchanged.
This will exclude nontrivial cycles of reachable states. -/
theorem energy_average_eq_iff (S : Finset V) (w : State V) :
    energy (average S w) = energy w ↔ average S w = w := by
  constructor
  · intro he
    have hzero : ∑ v ∈ S, (w v - mean S w) ^ 2 = 0 := by
      rw [← energy_drop, he, sub_self]
    have hv := (Finset.sum_eq_zero_iff_of_nonneg
      (fun v (_ : v ∈ S) => sq_nonneg (w v - mean S w))).mp hzero
    funext v
    by_cases hmem : v ∈ S
    · rw [average_apply_mem S w hmem]
      have := hv v hmem
      nlinarith [sq_nonneg (w v - mean S w)]
    · exact average_apply_not_mem S w hmem
  · intro h
    rw [h]

/-!
## Preparation for duality: self-adjointness and affine maps

These identities support reverse profiles and the shorter-arm transformations in Paper 2.
-/

/-- Averaging is self-adjoint for `pairing`; this is the basis of reverse-profile duality. -/
theorem average_selfAdjoint (S : Finset V) (u w : State V) :
    pairing (average S u) w = pairing u (average S w) := by
  have hinside : (∑ v ∈ S, average S u v * w v) = ∑ v ∈ S, u v * average S w v := by
    calc
      _ = mean S u * (∑ v ∈ S, w v) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun v hv => by rw [average_apply_mem S u hv])
      _ = (∑ v ∈ S, u v) * mean S w := by
        unfold mean
        ring
      _ = _ := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun v hv => by rw [average_apply_mem S w hv])
  have houtside : (∑ v ∈ Sᶜ, average S u v * w v) = ∑ v ∈ Sᶜ, u v * average S w v := by
    apply Finset.sum_congr rfl
    intro v hv
    have hv' : v ∉ S := Finset.mem_compl.mp hv
    rw [average_apply_not_mem S u hv', average_apply_not_mem S w hv']
  unfold pairing
  rw [← Finset.sum_add_sum_compl S (fun v => average S u v * w v),
    ← Finset.sum_add_sum_compl S (fun v => u v * average S w v), hinside, houtside]

/-- Every constant state is fixed, including by the empty-set average. -/
theorem average_const (S : Finset V) (c : ℝ) :
    average S (fun _ : V => c) = fun _ => c := by
  funext v
  by_cases hv : v ∈ S
  · rw [average_apply_mem S _ hv, mean_eq_expect]
    exact Finset.expect_const ⟨v, hv⟩ c
  · exact average_apply_not_mem S _ hv

/-- Averaging commutes with real affine transformations, including negative scaling. -/
theorem average_affine (S : Finset V) (w : State V) (a b : ℝ) :
    average S (fun v => a * w v + b) = fun v => a * average S w v + b := by
  change averageLinear S (a • w + fun _ => b) = a • averageLinear S w + fun _ => b
  rw [map_add, map_smul]
  exact congrArg (fun u : State V => a • averageLinear S w + u) (average_const S b)

end WaterTransport
