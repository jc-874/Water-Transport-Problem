import WaterTransport2.S04_Main

/-!
# Paper 2: definitions and Theorems 1, 2, and 3

The shared model is documented in `WaterTransport1.lean`: a state is a real
vector, a legal move averages a nonempty induced connected set, and `run`
executes a finite list from left to right. `optimalLength` is the least length
of a globally optimal single-target strategy.

All paper-specific definitions below are transparent aliases of the existing
definitions in `WaterTransport2/`. Their mathematical contents are recorded
here for review. Proofs remain in those numbered modules.
-/

open WaterTransport

namespace WaterTransport2

/-! ## Definitions: the three-arm spider and the reference construction -/

/-- `Fin (m+3)`, labelled `a_0, ..., a_m, b, c` in that order. -/
abbrev Vertex (m : ℕ) := WaterTransport.Paper2.Vertex m

/-- The root `o = a_0`, represented by vertex `0`. -/
abbrev root (m : ℕ) : Vertex m := WaterTransport.Paper2.root m

/-- The short leaf `b`, represented by vertex `m+1`. -/
abbrev leafB (m : ℕ) : Vertex m := WaterTransport.Paper2.leafB m

/-- The short leaf `c`, represented by vertex `m+2`. -/
abbrev leafC (m : ℕ) : Vertex m := WaterTransport.Paper2.leafC m

/-- `S(m,1,1)`: the edges are `a_i--a_(i+1)` for `i < m`, and `o--b`, `o--c`.
The main results assume `m ≥ 2`; the definitions also allow smaller parameters. -/
abbrev spider (m : ℕ) : SimpleGraph (Vertex m) := WaterTransport.Paper2.spider m

/-- The long-arm prefix `P_j = {a_i | i ≤ j and i ≤ m}`. -/
abbrev pathPrefix (m j : ℕ) : Finset (Vertex m) :=
  WaterTransport.Paper2.pathPrefix m j

/-- The chronological construction of `p_m` from root unit mass:
first `P_m`, `P_(m-1) ∪ {b}`, `P_(m-1) ∪ {c}`; then, for
`j = m-2, m-3, ..., 0`, use `P_j ∪ {b}` when `m-j` is even and
`P_j ∪ {c}` when it is odd. There are `m+2` moves when `m ≥ 2`. -/
abbrev referenceStrategy (m : ℕ) : Strategy (Vertex m) :=
  WaterTransport.Paper2.referenceStrategy m

/-- The reference vector `p_m = run (referenceStrategy m) e_o`,
where `e_o(o)=1` and all other coordinates of `e_o` are zero.
This is a state vector, not an operation list. -/
noncomputable abbrev referenceProfile (m : ℕ) : State (Vertex m) :=
  WaterTransport.Paper2.referenceProfile m

/-! ## Definitions: reachable profiles, minimum realization length, and order -/

/-- `R_k = {run σ e_o | σ is legal and σ.length ≤ k}`, including zero steps.
No closure is taken. -/
abbrev profilesWithin (m k : ℕ) : Set (State (Vertex m)) :=
  WaterTransport.Paper2.profilesWithin m k

/-- `R_fin = {run σ e_o | σ is a finite legal strategy} = ⋃ k, R_k`. -/
abbrev reachableProfiles (m : ℕ) : Set (State (Vertex m)) :=
  WaterTransport.Paper2.reachableProfiles m

/-- `ℓ(q) = min {σ.length | σ is legal and run σ e_o = q}`.
The reachability argument ensures this minimum exists. It concerns the whole
profile, not the water level at a single vertex. -/
noncomputable abbrev profileLength (m : ℕ) (q : State (Vertex m))
    (hq : q ∈ reachableProfiles m) : ℕ :=
  WaterTransport.Paper2.profileLength m q hq

/-- `Λ_m(q) = (q(a_m), -q(a_(m-1)), ..., (-1)^m q(a_0))`.
Only the long-arm coordinates enter this vector; `b` and `c` are omitted. -/
noncomputable abbrev comparisonVector (m : ℕ) (q : State (Vertex m)) :
    Fin (m + 1) → ℝ :=
  WaterTransport.Paper2.comparisonVector m q

/-- Strict lexicographic order:
`∃ r, (∀ s < r, u s = v s) ∧ u r < v r`. -/
abbrev LexLess {n : ℕ} (u v : Fin n → ℝ) : Prop :=
  WaterTransport.Paper2.LexLess u v

/-- Nonstrict lexicographic order: `u = v ∨ LexLess u v`. -/
abbrev LexLE {n : ℕ} (u v : Fin n → ℝ) : Prop :=
  WaterTransport.Paper2.LexLE u v

/-! ## Theorem 1: lexicographic maximality and the equality-case length bound -/

/-- **Theorem 1**, with all three clauses of the paper:
every reachable profile is lexicographically bounded by `p_m`; equality of
comparison vectors requires at least `m+2` moves; profiles reachable within
`m+1` moves are strictly smaller. Equality need not mean equality of all vertices. -/
theorem theorem_1 (m : ℕ) (hm : 2 ≤ m) :
    (∀ q ∈ reachableProfiles m,
      LexLE (comparisonVector m q) (comparisonVector m (referenceProfile m))) ∧
    (∀ q, ∀ hq : q ∈ reachableProfiles m,
      comparisonVector m q = comparisonVector m (referenceProfile m) →
        m + 2 ≤ profileLength m q hq) ∧
    (∀ q ∈ profilesWithin m (m + 1),
      LexLess (comparisonVector m q) (comparisonVector m (referenceProfile m))) :=
  ⟨WaterTransport.Paper2.profile_lex_maximal m hm,
    WaterTransport.Paper2.profile_length_of_comparison_eq m hm,
    WaterTransport.Paper2.short_profile_lex_lt m hm⟩

/-! ## Definitions for Theorem 2: explicit nonnegative integer weights -/

/-- The integer base `Q = 4 (m+3)^(2(m+2))`. -/
abbrev weightBase (m : ℕ) : ℕ := WaterTransport.Paper2.weightBase m

/-- The constant offset `B = Q^(m-1)`. -/
abbrev weightOffset (m : ℕ) : ℕ := WaterTransport.Paper2.weightOffset m

/-- Equation (5.2): `w_m(a_i) = B + (-1)^(m-i) Q^i` for `0 ≤ i ≤ m`,
and `w_m(b) = w_m(c) = B`. All signed arithmetic is in `ℤ`. -/
abbrev integerWeights (m : ℕ) (v : Vertex m) : ℤ :=
  WaterTransport.Paper2.integerWeights m v

/-- The same integer weights embedded into real states:
`weights m v = (integerWeights m v : ℝ)`. -/
abbrev weights (m : ℕ) : State (Vertex m) := WaterTransport.Paper2.weights m

/-- The finite inner product `⟨q,w⟩ = ∑ v, q v * w v`. -/
noncomputable abbrev pairing (m : ℕ) (q w : State (Vertex m)) : ℝ :=
  WaterTransport.pairing q w

/-- **Theorem 2.** The explicit integer input is nonnegative, and its pairing
with `p_m` is strictly larger than its pairing with any profile in `R_(m+1)`. -/
theorem theorem_2 (m : ℕ) (hm : 2 ≤ m) :
    Nonnegative (weights m) ∧
    ∀ q ∈ profilesWithin m (m + 1),
      pairing m q (weights m) < pairing m (referenceProfile m) (weights m) :=
  ⟨WaterTransport.Paper2.weights_nonnegative m hm,
    WaterTransport.Paper2.short_profile_reward_lt m hm⟩

/-! ## Theorem 3: arbitrarily long shortest optimal strategies -/

/-- **Theorem 3.** The shortest globally optimal strategy for the root of
`S(m,1,1)`, with initial weights `w_m`, has length at least `m+2`.
The nonnegativity argument is supplied by Theorem 2. This is a lower bound,
not an assertion that the reversed reference construction is globally optimal. -/
theorem theorem_3 (m : ℕ) (hm : 2 ≤ m) :
    m + 2 ≤ optimalLength (spider m) (weights m) (theorem_2 m hm).1 (root m) :=
  WaterTransport.Paper2.optimalLength_lower_bound m hm

/-- The consequence stated after Theorem 3: shortest optimal lengths are
unbounded even among graphs of maximum degree at most three. The number of
vertices is allowed to grow. -/
theorem theorem_3_unbounded (K : ℕ) :
    ∃ m : ℕ, ∃ hm : 2 ≤ m,
      (∀ v, (spider m).degree v ≤ 3) ∧
      K < optimalLength (spider m) (weights m) (theorem_2 m hm).1 (root m) :=
  WaterTransport.Paper2.no_uniform_bound K

end WaterTransport2
