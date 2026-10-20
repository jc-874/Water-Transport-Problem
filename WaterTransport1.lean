import WaterTransport1.S09_Stars
import WaterTransport1.S11_Examples

/-!
# Paper 1: definitions and main results

Read this file to review Theorem 2.1, Corollary 2.1, Theorem 3.1, and Theorem 4.1.
The definitions below are transparent aliases of the shared model, not a second
implementation. Each theorem cites its checked proof in `WaterTransport1/`.
The numbered modules contain the proofs, auxiliary results, and examples.

All graphs in this formalization are finite undirected simple graphs. Strategies
are finite, may repeat moves, and may have length zero. Reachability is exact:
no topological closure is included.
-/

namespace WaterTransport1

/-! ## Shared definitions: states, legal averaging, and finite execution -/

/-- A water-level vector: `State V = V → ℝ`. -/
abbrev State (V : Type*) := WaterTransport.State V

/-- Physical initial states: `Nonnegative w` means `∀ v, 0 ≤ w v`. -/
abbrev Nonnegative {V : Type*} (w : State V) : Prop :=
  WaterTransport.Nonnegative w

/-- A finite list of selected vertex sets, in chronological order. -/
abbrev Strategy (V : Type*) := WaterTransport.Strategy V

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `S.Nonempty ∧ (G.induce (S : Set V)).Connected`.
Connectivity is required inside the selected set, not just in the ambient graph. -/
abbrev IsLegalMove (G : SimpleGraph V) (S : Finset V) : Prop :=
  WaterTransport.IsLegalMove G S

/-- Complete averaging: on `S`, replace each coordinate by
`(∑ u ∈ S, w u) / |S|`; outside `S`, leave the coordinate unchanged.
Only nonempty connected sets are allowed as moves. -/
noncomputable abbrev average (S : Finset V) (w : State V) : State V :=
  WaterTransport.average S w

/-- Every move in the list is legal: `∀ S ∈ σ, IsLegalMove G S`. -/
abbrev IsLegal (G : SimpleGraph V) (σ : Strategy V) : Prop :=
  WaterTransport.IsLegal G σ

/-- Execute from left to right: `run [] w = w` and
`run (S :: σ) w = run σ (average S w)`. -/
noncomputable abbrev run (σ : Strategy V) (w : State V) : State V :=
  WaterTransport.run σ w

/-- Exact finite reachability: `∃ σ, IsLegal G σ ∧ run σ w = u`. -/
abbrev Reachable (G : SimpleGraph V) (w u : State V) : Prop :=
  WaterTransport.Reachable G w u

/-! ## Shared definitions: objectives, global optimality, and minimum length -/

/-- The supremum of `{f u | Reachable G w u}` over all finite legal strategies.
Theorem 2.1 below proves attainment under the stated continuity assumption. -/
noncomputable abbrev optimalValue (G : SimpleGraph V) (f : State V → ℝ)
    (w : State V) : ℝ :=
  WaterTransport.optimalValue G f w

/-- The single-target supremum: `optimalValue G (fun u => u x) w`. -/
noncomputable abbrev targetSup (G : SimpleGraph V) (w : State V) (x : V) : ℝ :=
  WaterTransport.targetSup G w x

/-- Global optimality for `f`: legality and
`∀ τ, IsLegal G τ → f (run τ w) ≤ f (run σ w)`. -/
abbrev IsOptimalFor (G : SimpleGraph V) (f : State V → ℝ) (w : State V)
    (σ : Strategy V) : Prop :=
  WaterTransport.IsOptimalFor G f w σ

/-- Global optimality at vertex `x`: `IsOptimalFor G (fun u => u x) w σ`. -/
abbrev IsOptimal (G : SimpleGraph V) (w : State V) (x : V)
    (σ : Strategy V) : Prop :=
  WaterTransport.IsOptimal G w x σ

/-- The paper's `t(G,x,w)`: the minimum of `σ.length` over `IsOptimal G w x σ`.
The argument `hw` supplies the domain on which existence has been proved;
the minimum is a natural number and may be zero. -/
noncomputable abbrev optimalLength (G : SimpleGraph V) (w : State V)
    (hw : Nonnegative w) (x : V) : ℕ :=
  WaterTransport.optimalLength G w hw x

/-! ## Theorem 2.1 and Corollary 2.1: finite attainment -/

/-- **Theorem 2.1.** Every objective continuous on the nonnegative cone attains
its supremum at a finitely reachable state. Continuity outside that cone is
not required. The graph need not be connected. -/
theorem theorem_2_1 (G : SimpleGraph V) (f : State V → ℝ)
    (hf : ContinuousOn f {u | Nonnegative u}) (w : State V) (hw : Nonnegative w) :
    ∃ u, Reachable G w u ∧ f u = optimalValue G f w :=
  WaterTransport.continuous_objective_attained G f hf w hw

/-- **Corollary 2.1.** A finite legal strategy attains the supremum at any
prescribed target vertex. -/
theorem corollary_2_1 (G : SimpleGraph V) (w : State V)
    (hw : Nonnegative w) (x : V) :
    ∃ σ, IsLegal G σ ∧ run σ w x = targetSup G w x :=
  WaterTransport.target_attained G w hw x

/-! ## Theorem 3.1: at most two moves on a path -/

/-- The path on vertices `0, ..., n-1`, with edges between consecutive indices.
An arbitrary finite path can be represented by this graph after relabelling. -/
abbrev pathGraph (n : ℕ) : SimpleGraph (Fin n) := SimpleGraph.pathGraph n

/-- **Theorem 3.1.** Every nonnegative state on a path has a globally optimal
single-target strategy of length at most two. -/
theorem theorem_3_1 {n : ℕ} (w : State (Fin n))
    (hw : Nonnegative w) (x : Fin n) :
    optimalLength (pathGraph n) w hw x ≤ 2 :=
  WaterTransport.path_optimalLength_le_two w hw x

/-! ## Theorem 4.1: at most one move per leaf for a star center -/

/-- The star `K_(1,n)` on `Fin (n+1)`, with center `0` and leaves `1, ..., n`.
Its edges are exactly the pairs of distinct vertices containing the center. -/
abbrev star (n : ℕ) : SimpleGraph (Fin (n + 1)) := WaterTransport.star n

/-- **Theorem 4.1.** On a star with `n` leaves, the central water level can be
maximized by a strategy of length at most `n`. -/
theorem theorem_4_1 (n : ℕ) (w : State (Fin (n + 1))) (hw : Nonnegative w) :
    optimalLength (star n) w hw 0 ≤ n :=
  WaterTransport.star_optimalLength_le n w hw

end WaterTransport1
