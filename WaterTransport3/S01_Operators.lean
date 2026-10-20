import WaterTransport1.S05_MinimalLength
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.DoublyStochasticMatrix
import Mathlib.Data.Nat.Log
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Paper 3, Sections 1-2: strategy polytopes and length bounds

Use Paper 1's `strategyMatrix`, preserving its averaging model and chronological
composition convention. Convex hulls here consist of finite convex combinations.
The recurrence for L_1, L_2, and L_n (n >= 3) is equation (2.9); L_0 = 0 extends it to empty graphs.

Reading order: operator sets and convex hulls; numerical bounds and local geometry
data; stochasticity and relabelling; mixing contraction; finite-horizon hull facts.
-/

namespace WaterTransport.Paper3

variable {V : Type*} [Fintype V] [DecidableEq V]

/-!
## Definitions: operator sets and ordinary convex hulls

Distinguish strategies within a fixed horizon from all finite strategies and define their finite-combination hulls.
-/

/-- Matrices realized by legal strategies of length at most `k`. -/
def operatorsWithin (G : SimpleGraph V) (k : ℕ) : Set (Matrix V V ℝ) :=
  {M | ∃ σ, IsLegal G σ ∧ σ.length ≤ k ∧ strategyMatrix σ = M}

/-- Matrices realized by arbitrary finite legal strategies. -/
def strategyOperators (G : SimpleGraph V) : Set (Matrix V V ℝ) :=
  {M | ∃ σ, IsLegal G σ ∧ strategyMatrix σ = M}

/-- The real convex hull of the operators within horizon `k`, using finite convex combinations. -/
def operatorPolytope (G : SimpleGraph V) (k : ℕ) : Set (Matrix V V ℝ) :=
  convexHull ℝ (operatorsWithin G k)

/-- The real convex hull of all finite legal strategy operators. -/
def operatorHull (G : SimpleGraph V) : Set (Matrix V V ℝ) :=
  convexHull ℝ (strategyOperators G)

/-- A rational polytope is the real convex hull of a finite set of rational matrices. -/
def IsRationalPolytope (K : Set (Matrix V V ℝ)) : Prop :=
  ∃ F : Finset (Matrix V V ℚ),
    K = convexHull ℝ ((fun M : Matrix V V ℚ => fun i j => (M i j : ℝ)) '' (F : Set _))

/-!
## Definitions: the uniform horizon and local geometric data

Record the recurrence, explicit bound, consensus matrix, entry norm, affine space, and local radius.
-/

/-- The integer ceiling of the base-two logarithm, with mathlib's natural-number conventions at small inputs. -/
def logCeil (n : ℕ) : ℕ := Nat.clog 2 n
/-- The paper's q_n = 4*n^2*ceil(log_2 n), used as a connected-window count. -/
def windowCount (n : ℕ) : ℕ := 4 * n ^ 2 * logCeil n

/-- Equation (2.9): L_0=L_1=0, L_2=1, and L_n=2*q_n*(L_(n-1)+1) for n at least three. -/
def uniformLength : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | k + 3 => 2 * windowCount (k + 3) * (uniformLength (k + 2) + 1)

/-- The explicit bound in Theorem 1.1. For `n >= 2`, the natural quotient `n! / 2` is exact. -/
def explicitBound (n : ℕ) : ℕ :=
  16 ^ (n - 2) * (n.factorial / 2) ^ 2 * logCeil n ^ (n - 2)

/-- The global averaging matrix J, with every entry equal to 1/|V|. -/
noncomputable def consensusMatrix : Matrix V V ℝ := fun _ _ => 1 / (Fintype.card V : ℝ)

/-- The largest absolute matrix entry, rather than an induced row-sum matrix norm. -/
noncomputable def maxEntryNorm (M : Matrix V V ℝ) : ℝ :=
  ‖(fun p : V × V => M p.1 p.2)‖

/-- The affine space of matrices with all row and column sums equal to one.
Entrywise nonnegativity is a separate property. -/
def affineStochastic : Set (Matrix V V ℝ) :=
  {M | (∀ i, ∑ j, M i j = 1) ∧ ∀ j, ∑ i, M i j = 1}

/-- The local replacement radius 1/(4*n^5) for connected graphs with at least three vertices. -/
noncomputable def localRadius (n : ℕ) : ℝ := 1 / (4 * (n : ℝ) ^ 5)

/-!
## Preparation: stochasticity, relabelling, and mixing contraction

Derive the matrix properties from the shared execution model and establish invariance under vertex bijections.
-/

/-- The shared averaging definition implies nonnegative entries and row and column sums equal to one. -/
theorem strategyMatrix_doublyStochastic (σ : Strategy V) :
    strategyMatrix σ ∈ doublyStochastic ℝ V := by
  refine mem_doublyStochastic_iff_sum.mpr ⟨?_, ?_, ?_⟩
  · intro i j
    exact run_nonnegative σ (fun v => by simp [pointMass]; split_ifs <;> norm_num) i
  · have hconst : run σ (fun _ => (1 : ℝ)) = fun _ => 1 := by
      induction σ with
      | nil => rfl
      | cons S σ ih => rw [run_cons, average_const, ih]
    intro i
    have h := congrFun (strategyMatrix_mulVec σ (fun _ => (1 : ℝ))) i
    simpa [Matrix.mulVec, dotProduct, hconst] using h
  · intro j
    simpa [strategyMatrix, mass, pointMass] using run_mass σ (pointMass j)

theorem strategyMatrix_reindex {U : Type*} [Fintype U] [DecidableEq U]
    (e : V ≃ U) (σ : Strategy V) :
    strategyMatrix (σ.map (Finset.map e.toEmbedding)) =
      Matrix.reindex e e (strategyMatrix σ) := by
  ext i j
  have h := run_map_equiv e σ (pointMass (e.symm j)) (e.symm i)
  have he : pointMass (e.symm j) ∘ e.symm = pointMass j := by
    funext v
    simp [pointMass]
  simpa only [he, Equiv.apply_symm_apply, strategyMatrix, Matrix.reindex_apply,
    Matrix.submatrix_apply] using h

theorem maxEntryNorm_reindex {U : Type*} [Fintype U] [DecidableEq U]
    (e : V ≃ U) (M : Matrix V V ℝ) :
    maxEntryNorm (Matrix.reindex e e M) = maxEntryNorm M := by
  unfold maxEntryNorm
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro p
    exact norm_le_pi_norm (fun p : V × V => M p.1 p.2) (e.symm p.1, e.symm p.2)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro p
    simpa only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply] using
      norm_le_pi_norm (fun p : U × U => (Matrix.reindex e e M) p.1 p.2) (e p.1, e p.2)

theorem consensusMatrix_reindex {U : Type*} [Fintype U] [DecidableEq U]
    (e : V ≃ U) : Matrix.reindex e e (consensusMatrix : Matrix V V ℝ) =
      (consensusMatrix : Matrix U U ℝ) := by
  ext i j
  simp [Matrix.reindex_apply, consensusMatrix, Fintype.card_congr e]

/-- Left multiplication by a stochastic matrix forms convex combinations of rows,
so it cannot increase the maximum-entry distance from consensus. -/
theorem maxEntryNorm_mul_consensus_le (P Q : Matrix V V ℝ)
    (hP : P ∈ doublyStochastic ℝ V) :
    maxEntryNorm (P * Q - consensusMatrix) ≤ maxEntryNorm (Q - consensusMatrix) := by
  change ‖(fun p : V × V => (P * Q - consensusMatrix : Matrix V V ℝ) p.1 p.2)‖ ≤
    maxEntryNorm (Q - consensusMatrix)
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  rintro ⟨i, j⟩
  have heq : (P * Q - consensusMatrix : Matrix V V ℝ) i j =
      ∑ k, P i k * (Q - consensusMatrix : Matrix V V ℝ) k j := by
    simp only [Matrix.sub_apply, Matrix.mul_apply, consensusMatrix, mul_sub,
      Finset.sum_sub_distrib, ← Finset.sum_mul, sum_row_of_mem_doublyStochastic hP,
      one_mul]
  rw [Real.norm_eq_abs, heq]
  calc
    _ ≤ ∑ k, |P i k * (Q - consensusMatrix : Matrix V V ℝ) k j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, P i k * maxEntryNorm (Q - consensusMatrix) := by
      apply Finset.sum_le_sum
      intro k _
      have hp := (mem_doublyStochastic_iff_sum.mp hP).1 i k
      rw [abs_mul, abs_of_nonneg hp]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [Real.norm_eq_abs, maxEntryNorm] using
          norm_le_pi_norm (fun p : V × V =>
            (Q - consensusMatrix : Matrix V V ℝ) p.1 p.2) (k, j)) hp
    _ = _ := by rw [← Finset.sum_mul, sum_row_of_mem_doublyStochastic hP, one_mul]; rfl

/-!
## Centered energy and finite-horizon hull lemmas

Introduce the energy used for mixing, then prove finiteness, monotonicity, and isomorphism transport of the hulls.
-/

/-- The centered sum of squares used in Paper 3: subtract the global mean before
squaring. Paper 1's `energy` is the uncentered sum of squares. -/
noncomputable def centeredEnergy (w : State V) : ℝ :=
  energy (w - fun _ => mean Finset.univ w)

private theorem operatorsWithin_subset (G : SimpleGraph V) (k : ℕ) :
    operatorsWithin G k ⊆ strategyOperators G := by
  rintro M ⟨σ, hσ, _, rfl⟩
  exact ⟨σ, hσ, rfl⟩

/-- A fixed finite horizon contains only finitely many strategy operators. -/
theorem operatorsWithin_finite (G : SimpleGraph V) (k : ℕ) :
    (operatorsWithin G k).Finite := by
  apply ((List.finite_length_le (Finset V) k).image strategyMatrix).subset
  rintro M ⟨σ, _, hlen, rfl⟩
  exact ⟨σ, hlen, rfl⟩

theorem operatorPolytope_subset_hull (G : SimpleGraph V) (k : ℕ) :
    operatorPolytope G k ⊆ operatorHull G :=
  convexHull_mono (operatorsWithin_subset G k)

theorem operatorPolytope_mono (G : SimpleGraph V) {k l : ℕ} (h : k ≤ l) :
    operatorPolytope G k ⊆ operatorPolytope G l := by
  apply convexHull_mono
  rintro M ⟨σ, hσ, hlen, rfl⟩
  exact ⟨σ, hσ, hlen.trans h, rfl⟩

theorem strategyMatrix_mem_polytope (G : SimpleGraph V) (σ : Strategy V)
    (hσ : IsLegal G σ) {k : ℕ} (hlen : σ.length ≤ k) :
    strategyMatrix σ ∈ operatorPolytope G k :=
  subset_convexHull ℝ _ ⟨σ, hσ, hlen, rfl⟩

/-- Graph isomorphisms transport the entire finite convex hull and preserve strategy length. -/
theorem operatorPolytope_map_iso {U : Type*} [Fintype U] [DecidableEq U]
    {G : SimpleGraph V} {H : SimpleGraph U} (e : G ≃g H) (k : ℕ)
    {M : Matrix V V ℝ} (hM : M ∈ operatorPolytope G k) :
    Matrix.reindex e.toEquiv e.toEquiv M ∈ operatorPolytope H k := by
  let f := Matrix.reindexLinearEquiv ℝ ℝ e.toEquiv e.toEquiv
  have hsub : operatorsWithin G k ⊆ f ⁻¹' operatorPolytope H k := by
    rintro M ⟨σ, hσ, hlen, rfl⟩
    change Matrix.reindex e.toEquiv e.toEquiv (strategyMatrix σ) ∈ operatorPolytope H k
    rw [← strategyMatrix_reindex]
    exact strategyMatrix_mem_polytope H _ (hσ.map_iso e) (by simpa using hlen)
  exact convexHull_min hsub ((convex_convexHull ℝ _).linear_preimage f.toLinearMap) hM

end WaterTransport.Paper3
