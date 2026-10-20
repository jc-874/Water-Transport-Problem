import WaterTransport3.S04_RepetitionExample
import WaterTransport3.S05_ExactSearch

/-!
# Paper 3: definitions and main results

Review Theorem 1.1, Corollary 1.2, and the exact-algorithm part of Proposition 7.1
here. Proofs and auxiliary constructions remain in `WaterTransport3/`.
Definitions below are transparent aliases, so they use exactly the objects
appearing in those proofs. The shared state, legality, execution, optimality,
and minimum-length definitions are documented in `WaterTransport1.lean`.

Scope: Proposition 7.1's binary bit-complexity bounds and NEXP membership are
not formalized. Section 6's deferred repetition certificates remain in
`S04_RepetitionExample`; none of the results stated below depends on them.
-/

open WaterTransport

namespace WaterTransport3

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Definitions: strategy operators and finite convex combinations -/

/-- The matrix of a chronological strategy: for `σ = [S_1, ..., S_k]`,
`A_σ = A_(S_k) ... A_(S_1)`; for `σ = []`, it is the identity.
Its entries are `strategyMatrix σ i j = run σ e_j i`, where `e_j` is unit mass
at `j`. Thus `A_σ w = run σ w`. -/
noncomputable abbrev strategyMatrix (σ : Strategy V) : Matrix V V ℝ :=
  WaterTransport.strategyMatrix σ

/-- `A_k(G) = {strategyMatrix σ | IsLegal G σ and σ.length ≤ k}`. -/
abbrev operatorsWithin (G : SimpleGraph V) (k : ℕ) : Set (Matrix V V ℝ) :=
  WaterTransport.Paper3.operatorsWithin G k

/-- All finite legal strategy operators, with no length bound. -/
abbrev strategyOperators (G : SimpleGraph V) : Set (Matrix V V ℝ) :=
  WaterTransport.Paper3.strategyOperators G

/-- `P_k(G) = convexHull ℝ (operatorsWithin G k)`.
Convex hulls consist of finite convex combinations; no closure is taken. -/
abbrev operatorPolytope (G : SimpleGraph V) (k : ℕ) : Set (Matrix V V ℝ) :=
  WaterTransport.Paper3.operatorPolytope G k

/-- `P(G) = convexHull ℝ (strategyOperators G)`. -/
abbrev operatorHull (G : SimpleGraph V) : Set (Matrix V V ℝ) :=
  WaterTransport.Paper3.operatorHull G

/-- A real matrix set is a rational polytope if it is the real convex hull of
some finite set of rational matrices, embedded entrywise into `ℝ`. -/
abbrev IsRationalPolytope (K : Set (Matrix V V ℝ)) : Prop :=
  WaterTransport.Paper3.IsRationalPolytope K

/-! ## Definitions: the explicit uniform horizon -/

/-- `r_n = ceil(log_2 n)`, implemented as `Nat.clog 2 n`. -/
abbrev logCeil (n : ℕ) : ℕ := WaterTransport.Paper3.logCeil n

/-- `q_n = 4 n² r_n`. -/
abbrev windowCount (n : ℕ) : ℕ := WaterTransport.Paper3.windowCount n

/-- Equation (2.9): `L_1 = 0`, `L_2 = 1`, and
`L_n = 2 q_n (L_(n-1) + 1)` for `n ≥ 3`.
The additional convention `L_0 = 0` covers the empty graph. -/
abbrev uniformLength (n : ℕ) : ℕ := WaterTransport.Paper3.uniformLength n

/-- `16^(n-2) (n!/2)² ceil(log_2 n)^(n-2)`.
For `n ≥ 2`, the natural-number division `n! / 2` is exact. -/
abbrev explicitBound (n : ℕ) : ℕ := WaterTransport.Paper3.explicitBound n

/-! ## Theorem 1.1: stabilization, rationality, and length estimates -/

/-- **Theorem 1.1, operator statement.** For every finite graph, the convex hull
of all strategy operators equals the convex hull at horizon `L_|V|`, and is a
rational polytope. A long operator is a convex combination of short operators;
it need not equal one individual short operator. -/
theorem theorem_1_1 (G : SimpleGraph V) :
    operatorHull G = operatorPolytope G (uniformLength (Fintype.card V)) ∧
    IsRationalPolytope (operatorHull G) :=
  ⟨WaterTransport.Paper3.uniform_convex_stabilization G,
    WaterTransport.Paper3.operatorHull_rationalPolytope G⟩

/-- **Theorem 1.1, explicit estimate.** The stated recurrence satisfies the
paper's factorial and logarithmic upper bound. -/
theorem theorem_1_1_bound (n : ℕ) (hn : 2 ≤ n) :
    uniformLength n ≤ explicitBound n :=
  WaterTransport.Paper3.uniformLength_le_explicitBound n hn

/-- **Theorem 1.1, asymptotic consequence.** The precise quantified meaning of
`L_n ≤ n^((2+o(1))n)`. The intermediate Stirling expansion in the paper is not
separately formalized. -/
theorem theorem_1_1_asymptotic :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (uniformLength n : ℝ) ≤ (n : ℝ) ^ ((2 + ε) * (n : ℝ)) :=
  WaterTransport.Paper3.uniformLength_asymptotic

/-! ## Corollary 1.2: short optimizers for every linear objective -/

/-- **Corollary 1.2.** For each real coefficient matrix `C`, some legal strategy
of length at most `L_|V|` maximizes `∑ i, ∑ j, C i j * A_σ i j` over every finite
legal strategy. This attained-maximum formulation expresses the paper's
equality between the unrestricted supremum and the bounded-horizon maximum. -/
theorem corollary_1_2 (G : SimpleGraph V) (C : Matrix V V ℝ) :
    ∃ σ : Strategy V, IsLegal G σ ∧ σ.length ≤ uniformLength (Fintype.card V) ∧
      ∀ τ : Strategy V, IsLegal G τ →
        (∑ i, ∑ j, C i j * strategyMatrix τ i j) ≤
          ∑ i, ∑ j, C i j * strategyMatrix σ i j :=
  WaterTransport.Paper3.linear_objective_attained G C

/-- **Corollary 1.2, single-target conclusion.** The shortest optimal length
is at most `L_|V|`, uniformly over all nonnegative inputs and all targets. -/
theorem corollary_1_2_target (G : SimpleGraph V) (w : State V)
    (hw : Nonnegative w) (x : V) :
    optimalLength G w hw x ≤ uniformLength (Fintype.card V) :=
  WaterTransport.Paper3.optimalLength_le_uniform G w hw x

/-! ## Definitions for Proposition 7.1: executable rational search -/

variable {n : ℕ}

/-- Enumerate all legal sets of size at least two, then all words of length at
most `L_n`, including the empty word. Evaluate them by exact rational averaging
and retain one attaining the largest target value. Singleton moves are identities.
This is the existing executable algorithm, not a choice of an unspecified maximizer. -/
abbrev exactSearch (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Fin n → ℚ) (x : Fin n) : Strategy (Fin n) :=
  WaterTransport.Paper3.exactSearch G w x

/-- The exact rational output value: `runQ (exactSearch G w x) w x`.
`runQ` uses the same averaging formula and chronological order as `run`, in `ℚ`. -/
abbrev exactValue (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Fin n → ℚ) (x : Fin n) : ℚ :=
  WaterTransport.Paper3.exactValue G w x

/-- The Boolean decision `decide (threshold < exactValue G w x)`.
The comparison is strict, as in the paper. -/
abbrev exceedsThreshold (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Fin n → ℚ) (x : Fin n) (threshold : ℚ) : Bool :=
  WaterTransport.Paper3.exceedsThreshold G w x threshold

/-! ## Proposition 7.1: exactness and decidability (complexity not formalized) -/

/-- **Proposition 7.1, exact optimization.** The executable search returns a
globally optimal legal strategy within `L_n`, and its rational output equals
the unrestricted real target supremum.
This statement does not assert the paper's bit running-time bounds. -/
theorem proposition_7_1_exact (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Fin n → ℚ) (hw : ∀ v, 0 ≤ w v) (x : Fin n) :
    IsOptimal G (fun v => (w v : ℝ)) x (exactSearch G w x) ∧
    (exactSearch G w x).length ≤ uniformLength n ∧
    targetSup G (fun v => (w v : ℝ)) x = (exactValue G w x : ℝ) :=
  ⟨(WaterTransport.Paper3.exactSearch_correct G w hw x).1,
    (WaterTransport.Paper3.exactSearch_correct G w hw x).2,
    WaterTransport.Paper3.rational_optimum G w hw x⟩

/-- **Proposition 7.1, threshold decision.** The Boolean answer is true exactly
when some finite legal strategy exceeds the specified rational threshold.
No NEXP membership assertion is included in this correctness theorem. -/
theorem proposition_7_1_threshold (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Fin n → ℚ) (hw : ∀ v, 0 ≤ w v) (x : Fin n) (threshold : ℚ) :
    exceedsThreshold G w x threshold = true ↔
      ∃ σ : Strategy (Fin n), IsLegal G σ ∧
        (threshold : ℝ) < run σ (fun v => (w v : ℝ)) x :=
  WaterTransport.Paper3.exceedsThreshold_correct G w hw x threshold

end WaterTransport3
