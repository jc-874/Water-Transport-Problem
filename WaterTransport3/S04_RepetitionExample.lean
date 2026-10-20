import WaterTransport3.S03_UniformBound
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Paper 3, Section 6: the five-vertex repetition example

Vertices 0,1,2,3,4 represent a,b,x,c,d, with target x = 2.

STATUS: the supplementary certificates for Lemma 6.1 were not supplied, and
their formalization is deferred at the user's request. Three explicit `sorry`
proofs remain below: the arbitrary-length, repetition-free, and three-step bounds.
They introduce `sorryAx`; AuditProgress reports their transitive dependencies.
The input data, legality, and concrete witness evaluations are proved independently.

Reading order: example data; verified evaluations; deferred certificate bounds;
conditional consequences depending on those bounds. The final group is not yet
an independently completed proof of the example's global claims.
-/

namespace WaterTransport.Paper3.RepetitionExample

/-!
## Definitions: the graph, initial state, and two witnesses

Use exact rational data, with target vertex 2.
-/

private def edges : Finset (Fin 5 × Fin 5) := {(0, 1), (1, 3), (1, 4), (2, 3), (2, 4)}

/-- The five-vertex graph with edges ab, bc, bd, xc, and xd. -/
def graph : SimpleGraph (Fin 5) := SimpleGraph.fromRel fun u v => (u, v) ∈ edges

instance : DecidableRel graph.Adj := by unfold graph; infer_instance

/-- Initial water levels (2,5,1,0,0) in the order a,b,x,c,d. -/
def weights : State (Fin 5) := ![2, 5, 1, 0, 0]
/-- The repeated-set four-move witness with verified final target level 65/32. -/
def witness : Strategy (Fin 5) := [{2, 3}, {1, 3}, {0, 1, 2, 4}, {2, 3}]
/-- A one-move repetition-free witness with verified final target level 2. -/
def repetitionFreeWitness : Strategy (Fin 5) := [{1, 2, 3}]

private def weightsQ : Fin 5 → ℚ := ![2, 5, 1, 0, 0]

/-!
## Verified calculations: legality and witness values

These proofs do not depend on the deferred bounds below.
-/

private theorem weights_cast : weights = fun v => (weightsQ v : ℝ) := by
  funext v
  fin_cases v <;> norm_num [weights, weightsQ]

theorem weights_nonnegative : Nonnegative weights := by
  intro v; fin_cases v <;> norm_num [weights]

theorem witness_legal : IsLegal graph witness := by
  unfold IsLegal IsLegalMove witness
  decide +kernel

theorem witness_value : run witness weights 2 = 65 / 32 := by
  rw [weights_cast, runQ_cast]
  change (runQ witness weightsQ 2 : ℝ) = 65 / 32
  rw [show runQ witness weightsQ 2 = 65 / 32 by decide +kernel]
  norm_num

theorem first_step_decreases : average ({2, 3} : Finset (Fin 5)) weights 2 = 1 / 2 := by
  change run [{2, 3}] weights 2 = 1 / 2
  rw [weights_cast, runQ_cast]
  change (runQ [{2, 3}] weightsQ 2 : ℝ) = 1 / 2
  rw [show runQ [{2, 3}] weightsQ 2 = 1 / 2 by decide +kernel]
  norm_num

theorem repetitionFreeWitness_legal : IsLegal graph repetitionFreeWitness := by
  unfold IsLegal IsLegalMove repetitionFreeWitness
  decide +kernel

theorem repetitionFreeWitness_nodup : RepetitionFree repetitionFreeWitness := by
  unfold RepetitionFree repetitionFreeWitness
  decide +kernel

theorem repetitionFreeWitness_value : run repetitionFreeWitness weights 2 = 2 := by
  rw [weights_cast, runQ_cast]
  change (runQ repetitionFreeWitness weightsQ 2 : ℝ) = 2
  rw [show runQ repetitionFreeWitness weightsQ 2 = 2 by decide +kernel]
  norm_num

/-!
## DEFERRED: three supplementary certificate bounds

Each of the following three declarations still contains sorry; their statements record the intended certificate obligations.
-/

/-- DEFERRED: the invariant K certificate in Lemma 6.1 gives the arbitrary-length upper bound. -/
theorem arbitrary_strategy_bound (σ : Strategy (Fin 5)) (hσ : IsLegal graph σ) :
    run σ weights 2 ≤ 65 / 32 := by
  sorry

/-- DEFERRED: the H certificate in Lemma 6.1 and the symmetry interchanging c and d give this bound. -/
theorem repetitionFree_bound (σ : Strategy (Fin 5)) (hσ : IsLegal graph σ)
    (hfree : RepetitionFree σ) : run σ weights 2 ≤ 2 := by
  sorry

/-- DEFERRED: the supplementary exact certificate for equation (6.6), covering at most three moves. -/
theorem three_step_bound (σ : Strategy (Fin 5)) (hσ : IsLegal graph σ)
    (hlen : σ.length ≤ 3) : run σ weights 2 ≤ 2 := by
  sorry

/-!
## Consequences depending on the deferred certificates

The following four conclusions inherit sorryAx and are explicitly tracked by AuditProgress.
-/

/-- DEPENDS ON DEFERRED CERTIFICATE: global witness optimality uses `arbitrary_strategy_bound`. -/
theorem witness_optimal : IsOptimal graph weights 2 witness := by
  refine ⟨witness_legal, ?_⟩
  intro σ hσ
  change run σ weights 2 ≤ run witness weights 2
  rw [witness_value]
  exact arbitrary_strategy_bound σ hσ

/-- DEPENDS ON DEFERRED CERTIFICATE: the exact global supremum follows from the pending witness-optimality claim. -/
theorem targetSup_value : targetSup graph weights 2 = 65 / 32 := by
  exact ((isOptimal_iff_attains graph weights weights_nonnegative 2 witness).mp
    witness_optimal).2.symm.trans witness_value

/-- DEPENDS ON DEFERRED CERTIFICATE: compare the witness with the pending bound on all repetition-free strategies. -/
theorem every_optimal_repeats (σ : Strategy (Fin 5)) (hσ : IsOptimal graph weights 2 σ) :
    ¬ RepetitionFree σ := by
  intro hfree
  have hlow : run witness weights 2 ≤ run σ weights 2 := hσ.2 witness witness_legal
  have hupp := repetitionFree_bound σ hσ.1 hfree
  rw [witness_value] at hlow
  linarith

/-- DEPENDS ON DEFERRED CERTIFICATE: global witness optimality and the pending three-step bound give minimum length four. -/
theorem shortest_length : optimalLength graph weights weights_nonnegative 2 = 4 := by
  have hupp := optimalLength_le graph weights weights_nonnegative 2 witness witness_optimal
  have hlen : witness.length = 4 := rfl
  obtain ⟨σ, hopt, hs⟩ := optimalLength_spec graph weights weights_nonnegative 2
  have hlow : 4 ≤ σ.length := by
    by_contra h
    have hval := three_step_bound σ hopt.1 (by omega)
    have hbest : run witness weights 2 ≤ run σ weights 2 := hopt.2 witness witness_legal
    rw [witness_value] at hbest
    linarith
  omega

end WaterTransport.Paper3.RepetitionExample
