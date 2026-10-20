import WaterTransport1.S01_Basic
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Set.Countable
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.NormNum
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.BigOperators

/-!
# Paper 1, Section 2: finite strategies and reachability

A strategy lists moves in chronological order: `[S, T]` averages `S` first.
The empty list is a zero-step strategy; singleton moves are legal identities.
Legality is a separate predicate, required in all optimization statements.

Reading order: model definitions; execution and invariants; finite-horizon
maxima; relabelling; reverse profiles and matrices; constant-block comparisons;
exact rational execution. Global optimality compares all finite legal strategies.
-/

namespace WaterTransport

variable {V : Type*} [Fintype V] [DecidableEq V]

/-!
## Definitions: finite execution, reachability, and optimality

Keep the strategy data separate from legality, and distinguish a bounded horizon from global optimality.
-/

/-- A finite chronological list of selected vertex sets. Graph legality is recorded by `IsLegal`. -/
abbrev Strategy (V : Type*) := List (Finset V)

/-- Every selected set is nonempty and induces a connected subgraph of `G`. -/
def IsLegal (G : SimpleGraph V) (σ : Strategy V) : Prop :=
  ∀ S ∈ σ, IsLegalMove G S

/-- Execute the list from left to right: `run [S,T] w = average T (average S w)`. -/
noncomputable def run : Strategy V → State V → State V
  | [], w => w
  | S :: σ, w => run σ (average S w)

/-- The paper's one-step relation: one legal average, which may leave the state unchanged. -/
def OneStep (G : SimpleGraph V) (w u : State V) : Prop :=
  ∃ S, IsLegalMove G S ∧ average S w = u

/-- Finite legal reachability, including zero steps. -/
def Reachable (G : SimpleGraph V) (w u : State V) : Prop :=
  ∃ σ, IsLegal G σ ∧ run σ w = u

/-- All states reachable in finitely many legal steps. No closure is taken. -/
def reachableSet (G : SimpleGraph V) (w : State V) : Set (State V) :=
  {u | Reachable G w u}

/-- States reachable in at most `k` steps, including the initial state. -/
def horizonStates (G : SimpleGraph V) (w : State V) (k : ℕ) : Set (State V) :=
  {u | ∃ σ, IsLegal G σ ∧ σ.length ≤ k ∧ run σ w = u}

/-- No repeated nontrivial selected set. Singleton identity moves are ignored. -/
def RepetitionFree (σ : Strategy V) : Prop :=
  (σ.filter fun S => 2 ≤ S.card).Nodup

/-- Legality and domination of every finite legal strategy for the objective `f`.
This predicate does not assume that an optimal strategy exists. -/
def IsOptimalFor (G : SimpleGraph V) (f : State V → ℝ) (w : State V)
    (σ : Strategy V) : Prop :=
  IsLegal G σ ∧ ∀ τ, IsLegal G τ → f (run τ w) ≤ f (run σ w)

/-- Global optimality for the water level at one target vertex. -/
def IsOptimal (G : SimpleGraph V) (w : State V) (x : V) (σ : Strategy V) : Prop :=
  IsOptimalFor G (fun u => u x) w σ

/-!
## Execution lemmas: lists, embeddings, and invariant quantities

Lift the one-move identities to finite strategies and compose reachability witnesses.
-/

@[simp] theorem isLegal_nil (G : SimpleGraph V) : IsLegal G [] := by
  simp [IsLegal]

@[simp] theorem isLegal_cons (G : SimpleGraph V) (S : Finset V) (σ : Strategy V) :
    IsLegal G (S :: σ) ↔ IsLegalMove G S ∧ IsLegal G σ := by
  simp [IsLegal, or_imp, forall_and]

@[simp] theorem run_nil (w : State V) : run [] w = w := rfl

@[simp] theorem run_cons (S : Finset V) (σ : Strategy V) (w : State V) :
    run (S :: σ) w = run σ (average S w) := rfl

@[simp] theorem run_singleton (S : Finset V) (w : State V) :
    run [S] w = average S w := rfl

theorem run_append (σ τ : Strategy V) (w : State V) :
    run (σ ++ τ) w = run τ (run σ w) := by
  induction σ generalizing w with
  | nil => rfl
  | cons S σ ih => exact ih (average S w)

/-- Transport execution through an embedding, for arm reduction and component lifting. -/
theorem run_map_embedding {U V : Type*} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
    (e : U ↪ V) (τ : Strategy U) (w : State V) (v : U) :
    run (τ.map (Finset.map e)) w (e v) = run τ (w ∘ e) v := by
  induction τ generalizing w with
  | nil => rfl
  | cons T τ ih =>
    rw [List.map_cons, run_cons, ih, run_cons]
    congr 1
    funext x
    simp [average, mean, Finset.sum_map]

/-- Moves supported in an embedding's image leave every outside coordinate unchanged. -/
theorem run_map_outside {U V : Type*} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
    (e : U ↪ V) (τ : Strategy U) (w : State V) (v : V) (hv : v ∉ Set.range e) :
    run (τ.map (Finset.map e)) w v = w v := by
  induction τ generalizing w with
  | nil => rfl
  | cons T τ ih =>
    rw [List.map_cons, run_cons, ih, average_apply_not_mem]
    intro h
    obtain ⟨u, _, hu⟩ := Finset.mem_map.mp h
    exact hv ⟨u, hu⟩

/-- Linear operator of a strategy, with composition ordered exactly as in `run`. -/
private noncomputable def runLinear : Strategy V → State V →ₗ[ℝ] State V
  | [] => LinearMap.id
  | S :: σ => (runLinear σ).comp (averageLinear S)

@[simp] private theorem runLinear_apply (σ : Strategy V) (w : State V) : runLinear σ w = run σ w := by
  induction σ generalizing w with
  | nil => rfl
  | cons S σ ih => exact ih (average S w)

theorem isLegal_append (G : SimpleGraph V) (σ τ : Strategy V) :
    IsLegal G (σ ++ τ) ↔ IsLegal G σ ∧ IsLegal G τ := by
  simp [IsLegal, or_imp, forall_and]

theorem reachable_refl (G : SimpleGraph V) (w : State V) : Reachable G w w :=
  ⟨[], isLegal_nil G, rfl⟩

theorem oneStep_reachable {G : SimpleGraph V} {w u : State V}
    (h : OneStep G w u) : Reachable G w u := by
  obtain ⟨S, hS, hu⟩ := h
  exact ⟨[S], by simpa using hS, hu⟩

theorem reachable_trans {G : SimpleGraph V} {w u z : State V}
    (hwu : Reachable G w u) (huz : Reachable G u z) : Reachable G w z := by
  obtain ⟨σ, hσ, rfl⟩ := hwu
  obtain ⟨τ, hτ, rfl⟩ := huz
  exact ⟨σ ++ τ, (isLegal_append G σ τ).mpr ⟨hσ, hτ⟩, run_append σ τ w⟩

theorem run_nonnegative (σ : Strategy V) {w : State V} (hw : Nonnegative w) :
    Nonnegative (run σ w) := by
  induction σ generalizing w with
  | nil => exact hw
  | cons S σ ih => exact ih (average_nonnegative S hw)

theorem run_mass (σ : Strategy V) (w : State V) : mass (run σ w) = mass w := by
  induction σ generalizing w with
  | nil => rfl
  | cons S σ ih => exact (ih (average S w)).trans (average_mass S w)

theorem run_energy_le (σ : Strategy V) (w : State V) : energy (run σ w) ≤ energy w := by
  induction σ generalizing w with
  | nil => exact le_rfl
  | cons S σ ih => exact (ih (average S w)).trans (energy_average_le S w)

/-- A strategy preserves energy exactly when its final state equals its initial state. -/
private theorem run_energy_eq_iff (σ : Strategy V) (w : State V) :
    energy (run σ w) = energy w ↔ run σ w = w := by
  induction σ generalizing w with
  | nil => simp
  | cons S σ ih =>
    constructor
    · intro he
      have hfirst : energy (average S w) = energy w :=
        le_antisymm (energy_average_le S w) (he ▸ run_energy_le σ (average S w))
      have hfix := (energy_average_eq_iff S w).mp hfirst
      simpa only [run_cons, hfix] using (ih w).mp (by simpa only [run_cons, hfix] using he)
    · intro h
      rw [h]

/-- Energy dissipation makes reachability antisymmetric. No global order instance is installed on states. -/
theorem reachable_antisymm {G : SimpleGraph V} {w u : State V}
    (hwu : Reachable G w u) (huw : Reachable G u w) : w = u := by
  obtain ⟨σ, _, rfl⟩ := hwu
  obtain ⟨τ, _, hτ⟩ := huw
  have he : energy (run σ w) = energy w :=
    le_antisymm (run_energy_le σ w) (by simpa only [hτ] using run_energy_le τ (run σ w))
  exact ((run_energy_eq_iff σ w).mp he).symm

theorem reachable_nonnegative {G : SimpleGraph V} {w u : State V}
    (hw : Nonnegative w) (hu : Reachable G w u) : Nonnegative u := by
  obtain ⟨σ, _, rfl⟩ := hu
  exact run_nonnegative σ hw

/-!
## Finite-horizon maxima

Countability holds for all reachable states; finiteness and attainment hold at every fixed horizon.
-/

/-- Finite words over the finite move alphabet give countably many reachable states. -/
theorem reachableSet_countable (G : SimpleGraph V) (w : State V) :
    (reachableSet G w).Countable := by
  apply (Set.countable_range (fun σ : Strategy V => run σ w)).mono
  rintro u ⟨σ, _, rfl⟩
  exact ⟨σ, rfl⟩

/-- A fixed horizon gives finitely many candidates, independently of global attainment. -/
private theorem horizonStates_finite (G : SimpleGraph V) (w : State V) (k : ℕ) :
    (horizonStates G w k).Finite := by
  apply ((List.finite_length_le (Finset V) k).image (fun σ => run σ w)).subset
  rintro u ⟨σ, _, hlen, rfl⟩
  exact ⟨σ, hlen, rfl⟩

/-- Target values after at most `t` steps, including the zero-step value. -/
def horizonValues (G : SimpleGraph V) (w : State V) (x : V) (t : ℕ) : Set ℝ :=
  (fun u => u x) '' horizonStates G w t

/-- The maximum target level within a fixed horizon, defined as a supremum and proved attained below. -/
noncomputable def horizonMax (G : SimpleGraph V) (w : State V) (x : V) (t : ℕ) : ℝ :=
  sSup (horizonValues G w x t)

private theorem horizonValues_nonempty (G : SimpleGraph V) (w : State V) (x : V) (t : ℕ) :
    (horizonValues G w x t).Nonempty :=
  ⟨w x, w, ⟨[], isLegal_nil G, Nat.zero_le t, rfl⟩, rfl⟩

private theorem horizonValues_finite (G : SimpleGraph V) (w : State V) (x : V) (t : ℕ) :
    (horizonValues G w x t).Finite :=
  (horizonStates_finite G w t).image _

/-- The finite nonempty set of horizon values has an attained maximum.
This needs neither nonnegative input nor the general existence theorem. -/
theorem horizonMax_attained (G : SimpleGraph V) (w : State V) (x : V) (t : ℕ) :
    ∃ σ, IsLegal G σ ∧ σ.length ≤ t ∧ run σ w x = horizonMax G w x t := by
  obtain ⟨u, ⟨σ, hσ, hlen, rfl⟩, hval⟩ :=
    (horizonValues_nonempty G w x t).csSup_mem (horizonValues_finite G w x t)
  exact ⟨σ, hσ, hlen, hval⟩

theorem le_horizonMax (G : SimpleGraph V) (w : State V) (x : V) (t : ℕ)
    (σ : Strategy V) (hσ : IsLegal G σ) (hlen : σ.length ≤ t) :
    run σ w x ≤ horizonMax G w x t :=
  le_csSup (horizonValues_finite G w x t).bddAbove ⟨run σ w, ⟨σ, hσ, hlen, rfl⟩, rfl⟩

theorem horizonMax_le (G : SimpleGraph V) (w : State V) (x : V) (t : ℕ) (b : ℝ)
    (hb : ∀ σ, IsLegal G σ → σ.length ≤ t → run σ w x ≤ b) :
    horizonMax G w x t ≤ b := by
  apply csSup_le (horizonValues_nonempty G w x t)
  rintro _ ⟨u, ⟨σ, hσ, hlen, rfl⟩, rfl⟩
  exact hb σ hσ hlen

theorem horizonMax_mono (G : SimpleGraph V) (w : State V) (x : V) {s t : ℕ}
    (hst : s ≤ t) : horizonMax G w x s ≤ horizonMax G w x t := by
  apply horizonMax_le
  intro σ hσ hlen
  exact le_horizonMax G w x t σ hσ (hlen.trans hst)

/-!
## Transport through graph isomorphisms

Relabel states and moves together, preserving execution, legality, and global optimality.
-/

/-- Averaging commutes with a bijective relabelling, coordinate by coordinate. -/
private theorem average_map_equiv {U : Type*} [Fintype U] [DecidableEq U]
    (e : V ≃ U) (S : Finset V) (w : State V) (v : V) :
    average (S.map e.toEmbedding) (w ∘ e.symm) (e v) = average S w v := by
  simp [average, mean]

/-- Relabelling every move commutes with executing the strategy. -/
theorem run_map_equiv {U : Type*} [Fintype U] [DecidableEq U]
    (e : V ≃ U) (σ : Strategy V) (w : State V) (v : V) :
    run (σ.map (Finset.map e.toEmbedding)) (w ∘ e.symm) (e v) = run σ w v := by
  induction σ generalizing w with
  | nil => simp [Function.comp_def]
  | cons S σ ih =>
    have ha : average (S.map e.toEmbedding) (w ∘ e.symm) = (average S w) ∘ e.symm := by
      funext x
      simpa only [Equiv.apply_symm_apply, Function.comp_apply] using
        average_map_equiv e S w (e.symm x)
    simpa only [List.map_cons, run_cons, ha] using ih (average S w)

/-- A graph isomorphism preserves legality of induced connected averaging sets. -/
theorem IsLegalMove.map_iso {U : Type*} [Fintype U] [DecidableEq U]
    {G : SimpleGraph V} {H : SimpleGraph U} (e : G ≃g H)
    {S : Finset V} (hS : IsLegalMove G S) :
    IsLegalMove H (S.map e.toEquiv.toEmbedding) := by
  let f : G.induce (S : Set V) →g H.induce (S.map e.toEquiv.toEmbedding : Set U) :=
    { toFun := fun v => ⟨e v.val, Finset.mem_map.mpr ⟨v.val, v.property, rfl⟩⟩
      map_rel' := fun h => e.map_rel_iff.mpr h }
  have hf : Function.Surjective f := by
    intro v
    obtain ⟨u, hu, heu⟩ := Finset.mem_map.mp v.property
    exact ⟨⟨u, hu⟩, Subtype.ext heu⟩
  exact ⟨hS.1.map, hS.2.map f hf⟩

theorem IsLegal.map_iso {U : Type*} [Fintype U] [DecidableEq U]
    {G : SimpleGraph V} {H : SimpleGraph U} (e : G ≃g H)
    {σ : Strategy V} (hσ : IsLegal G σ) :
    IsLegal H (σ.map (Finset.map e.toEquiv.toEmbedding)) := by
  intro T hT
  obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hT
  exact (hσ S hS).map_iso e

/-- Graph isomorphisms transport global optimality, with all finite legal competitors. -/
theorem IsOptimal.map_iso {U : Type*} [Fintype U] [DecidableEq U]
    {G : SimpleGraph V} {H : SimpleGraph U} (e : G ≃g H)
    {σ : Strategy V} {w : State V} {x : V} (hσ : IsOptimal G w x σ) :
    IsOptimal H (w ∘ e.symm) (e x) (σ.map (Finset.map e.toEquiv.toEmbedding)) := by
  refine ⟨hσ.1.map_iso e, ?_⟩
  intro τ hτ
  have h := hσ.2 _ (hτ.map_iso e.symm)
  have hw : (w ∘ e.symm) ∘ e = w := by funext v; simp
  have he := run_map_equiv e.symm.toEquiv τ (w ∘ e.symm) (e x)
  change run (τ.map (Finset.map e.symm.toEquiv.toEmbedding))
    ((w ∘ e.symm) ∘ e) (e.symm (e x)) = run τ (w ∘ e.symm) (e x) at he
  rw [hw, e.symm_apply_apply] at he
  change run τ (w ∘ e.symm) (e x) ≤
    run (σ.map (Finset.map e.toEquiv.toEmbedding)) (w ∘ e.symm) (e x)
  exact he.symm.le.trans (h.trans_eq (run_map_equiv e.toEquiv σ w x).symm)


/-!
## Reverse profiles and strategy matrices

Self-adjointness reverses the chronological order in the pairing identity.
These interfaces are shared by the path and star proofs and by Papers 2 and 3.
-/

/-- Unit mass at the target `x`. -/
def pointMass (x : V) : State V := fun v => if v = x then 1 else 0

/-- Run the reversed strategy from unit mass at `x`.
The resulting profile depends on the strategy and target, not on the initial water levels. -/
noncomputable def reverseProfile (σ : Strategy V) (x : V) : State V :=
  run σ.reverse (pointMass x)

/-- The final target value equals the pairing of the reverse profile with the initial state. -/
theorem reverseProfile_duality (σ : Strategy V) (w : State V) (x : V) :
    run σ w x = pairing (reverseProfile σ x) w := by
  induction σ generalizing w with
  | nil => simp [reverseProfile, run, pairing, pointMass]
  | cons S σ ih =>
    rw [run_cons, ih]
    simp only [reverseProfile, List.reverse_cons, run_append, run_singleton]
    exact (average_selfAdjoint S (run σ.reverse (pointMass x)) w).symm

theorem reverseProfile_nonnegative (σ : Strategy V) (x : V) :
    Nonnegative (reverseProfile σ x) := by
  apply run_nonnegative
  intro v
  simp only [pointMass]
  split_ifs <;> norm_num

theorem reverseProfile_mass (σ : Strategy V) (x : V) : mass (reverseProfile σ x) = 1 := by
  rw [reverseProfile, run_mass]
  simp [mass, pointMass]

/-- Entry `(v,u)` is the amount arriving at `v` from unit mass at `u` after one average.
The matrix is derived from `average`, so it uses the same operation model. -/
noncomputable def averagingMatrix (S : Finset V) : Matrix V V ℝ :=
  fun v u => average S (pointMass u) v

/-- Column `u` is the final state obtained from unit mass at `u`; multiplication on a state reproduces `run`. -/
noncomputable def strategyMatrix (σ : Strategy V) : Matrix V V ℝ :=
  fun v u => run σ (pointMass u) v

theorem strategyMatrix_mulVec (σ : Strategy V) (w : State V) :
    (strategyMatrix σ).mulVec w = run σ w := by
  have hw : (∑ i, w i • pointMass i) = w := by
    funext v
    simp [pointMass, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite]
  funext v
  have h := congrArg (fun u : State V => u v) (congrArg (runLinear σ) hw)
  simp only [map_sum, map_smul, runLinear_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul] at h
  change (∑ i, run σ (pointMass i) v * w i) = run σ w v
  simpa only [mul_comm] using h

/-- Composition convention: executing the first strategy and then the second gives the second matrix times the first. -/
theorem strategyMatrix_append (σ τ : Strategy V) :
    strategyMatrix (σ ++ τ) = strategyMatrix τ * strategyMatrix σ := by
  ext v u
  change run (σ ++ τ) (pointMass u) v = _
  rw [run_append]
  exact (congrFun (strategyMatrix_mulVec τ (run σ (pointMass u))) v).symm

/-!
## Constant-block algebra for shorter-strategy comparisons

With total mass fixed, a linear objective on two constant blocks is affine in
one block height. A profile between two candidates cannot exceed both candidates.
All results in this section allow arbitrary real states.
-/

/-- A state constant on `S` and zero outside `S`. -/
def profileBlock (S : Finset V) (c : ℝ) : State V :=
  fun v => if v ∈ S then c else 0

@[simp] private theorem mass_profileBlock (S : Finset V) (c : ℝ) :
    mass (profileBlock S c) = S.card * c := by
  simp [mass, profileBlock]

@[simp] private theorem pairing_profileBlock (S : Finset V) (c : ℝ) (w : State V) :
    pairing (profileBlock S c) w = S.card * c * mean S w := by
  simp only [pairing, profileBlock, ite_mul, zero_mul, Finset.sum_ite_mem,
    Finset.univ_inter]
  rw [← Finset.mul_sum, ← card_mul_mean]
  ring

@[simp] private theorem mass_add (p q : State V) : mass (p + q) = mass p + mass q := by
  simp [mass, Finset.sum_add_distrib]

@[simp] private theorem pairing_add_left (p q w : State V) :
    pairing (p + q) w = pairing p w + pairing q w := by
  simp [pairing, add_mul, Finset.sum_add_distrib]

/-- Two constant blocks with fixed total mass give an affine one-parameter family.
An intermediate profile is bounded by the larger of two endpoint objective values.
The common remainder `base` need not have disjoint support from the blocks. -/
theorem pairing_le_max_of_two_blocks (S T : Finset V) (base w : State V)
    (a b a₀ b₀ a₁ b₁ : ℝ)
    (hm₀ : mass (base + profileBlock S a + profileBlock T b) =
      mass (base + profileBlock S a₀ + profileBlock T b₀))
    (hm₁ : mass (base + profileBlock S a + profileBlock T b) =
      mass (base + profileBlock S a₁ + profileBlock T b₁))
    (hb₀ : b₀ ≤ b) (hb₁ : b ≤ b₁) :
    pairing (base + profileBlock S a + profileBlock T b) w ≤
      max (pairing (base + profileBlock S a₀ + profileBlock T b₀) w)
        (pairing (base + profileBlock S a₁ + profileBlock T b₁) w) := by
  simp only [mass_add, mass_profileBlock] at hm₀ hm₁
  simp only [pairing_add_left, pairing_profileBlock]
  have hT : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
  by_cases h : mean S w ≤ mean T w
  · apply le_trans _ (le_max_right _ _)
    have hh := mul_nonneg hT
      (mul_nonneg (sub_nonneg.mpr hb₁) (sub_nonneg.mpr h))
    have he : (S.card * a + T.card * b - (S.card * a₁ + T.card * b₁)) *
        mean S w = 0 := by rw [show S.card * a + T.card * b =
          S.card * a₁ + T.card * b₁ by linarith]; ring
    nlinarith
  · apply le_trans _ (le_max_left _ _)
    have hh := mul_nonneg hT
      (mul_nonneg (sub_nonneg.mpr hb₀) (sub_nonneg.mpr (le_of_not_ge h)))
    have he : (S.card * a + T.card * b - (S.card * a₀ + T.card * b₀)) *
        mean S w = 0 := by rw [show S.card * a + T.card * b =
          S.card * a₀ + T.card * b₀ by linarith]; ring
    nlinarith

/-- The mean of a constant block is determined by an intersection cardinality. -/
theorem mean_profileBlock (S T : Finset V) (c : ℝ) :
    mean S (profileBlock T c) = (S ∩ T).card * c / S.card := by
  simp [mean, profileBlock, Finset.sum_ite_mem]

/-- Averaging spreads the intersection mass over the new set and fixes the exposed part of the old block. -/
private theorem average_profileBlock (S T : Finset V) (c : ℝ) :
    average S (profileBlock T c) =
      profileBlock S (mean S (profileBlock T c)) + profileBlock (T \ S) c := by
  funext v
  by_cases hS : v ∈ S <;> by_cases hT : v ∈ T <;>
    simp [average, profileBlock, hS, hT]

/-- Averaging a set containing the point mass produces the uniform probability profile on that set. -/
theorem average_pointMass (S : Finset V) (x : V) (hx : x ∈ S) :
    average S (pointMass x) = profileBlock S (1 / S.card) := by
  have hm : mean S (pointMass x) = 1 / S.card := by
    simp [mean, pointMass, hx]
  funext v
  by_cases hv : v ∈ S
  · simp [average, profileBlock, hv, hm]
  · have hne : v ≠ x := fun he => hv (he ▸ hx)
    simp [average, profileBlock, pointMass, hv, hne]

/-- Adding only vertices outside a nonnegative constant block cannot increase its mean. -/
theorem mean_profileBlock_antitone (S T U : Finset V) (hS : S.Nonempty)
    (hST : S ⊆ T) (hi : S ∩ U = T ∩ U) (c : ℝ) (hc : 0 ≤ c) :
    mean T (profileBlock U c) ≤ mean S (profileBlock U c) := by
  rw [mean_profileBlock, mean_profileBlock, hi]
  exact div_le_div_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) hc)
    (by exact_mod_cast Finset.card_pos.mpr hS)
    (by exact_mod_cast Finset.card_le_card hST)

/-- The mean of a nonnegative unit-mass profile on `S` is at most `1 / |S|`.
The auxiliary empty-set convention also satisfies this bound. -/
theorem mean_le_inv_card_of_probability (S : Finset V) (p : State V)
    (hp : Nonnegative p) (hm : mass p = 1) : mean S p ≤ 1 / S.card := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [← hm]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    (fun v _ _ => hp v)

/-!
## Exact rational execution and removal of identity moves

Connect executable rational calculations to real-valued theorems, then remove trivial operations.
-/

/-- Exact rational averaging, shared by the three papers' finite computations.
`runQ_cast` proves coordinatewise agreement with real execution. -/
def averageQ (S : Finset V) (w : V → ℚ) : V → ℚ :=
  fun v => if v ∈ S then (∑ u ∈ S, w u) / S.card else w v

def runQ : Strategy V → (V → ℚ) → (V → ℚ)
  | [], w => w
  | S :: σ, w => runQ σ (averageQ S w)

private theorem averageQ_cast (S : Finset V) (w : V → ℚ) :
    average S (fun v => (w v : ℝ)) = fun v => (averageQ S w v : ℝ) := by
  funext v
  by_cases hv : v ∈ S <;> simp [average, mean, averageQ, hv]

theorem runQ_cast (σ : Strategy V) (w : V → ℚ) :
    run σ (fun v => (w v : ℝ)) = fun v => (runQ σ w v : ℝ) := by
  induction σ generalizing w with
  | nil => rfl
  | cons S σ ih => simpa only [run_cons, averageQ_cast, runQ] using ih (averageQ S w)

/-- Removing empty and singleton identity moves leaves the executed state unchanged. -/
theorem run_filter_nontrivial (σ : Strategy V) (w : State V) :
    run (σ.filter (fun S => 2 ≤ S.card)) w = run σ w := by
  induction σ generalizing w with
  | nil => rfl
  | cons S σ ih =>
    by_cases hS : 2 ≤ S.card
    · simpa [hS, run] using ih (average S w)
    · have hid : average S w = w := by
        by_cases h0 : S.card = 0
        · rw [Finset.card_eq_zero.mp h0, average_empty]
        · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp (show S.card = 1 by omega)
          exact average_singleton v w
      simpa [hS, run, hid] using ih w

end WaterTransport
