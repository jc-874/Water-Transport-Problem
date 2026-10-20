import WaterTransport1.S05_MinimalLength
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# Paper 2: the three-arm spider and its reference profile

Reuse the complete averaging model, legality, execution, and optimality from
Paper 1. New objects live in `WaterTransport.Paper2`.
Vertices 0,...,m represent a_0,...,a_m; m+1 and m+2 represent the short leaves b,c.
The graph is defined for all `m` to support induction; the main theorems assume `2 <= m`.

Reading order: graph and degree bound; effective moves and arm sums; reference
strategy and profile; reachable profiles and minimum length; legality of the construction.
-/

namespace WaterTransport.Paper2

/-!
## Definition 1: labelled spider and degree bound

Specify the root, long-arm tip, and short leaves, then prove the maximum degree is at most three.
-/

/-- The `m + 3` labelled vertices of the spider. -/
abbrev Vertex (m : ℕ) := Fin (m + 3)

def root (m : ℕ) : Vertex m := 0
def tip (m : ℕ) : Vertex m := ⟨m, by omega⟩
def leafB (m : ℕ) : Vertex m := ⟨m + 1, by omega⟩
def leafC (m : ℕ) : Vertex m := ⟨m + 2, by omega⟩

/-- Definition 1: the long path arm with two short leaves at its root.
`fromRel` symmetrizes the edge relation and removes loops. -/
def spider (m : ℕ) : SimpleGraph (Vertex m) :=
  SimpleGraph.fromRel fun u v =>
    (u.val < m ∧ v.val = u.val + 1) ∨ (u = root m ∧ m < v.val)

instance (m : ℕ) : DecidableRel (spider m).Adj := by unfold spider; infer_instance

/-- Every vertex has degree at most three, as a consequence of the explicit graph definition. -/
theorem spider_degree_le_three (m : ℕ) (v : Vertex m) : (spider m).degree v ≤ 3 := by
  classical
  let candidates : Finset ℕ :=
    if v.val = 0 then {1, m + 1, m + 2} else {0, v.val - 1, v.val + 1}
  have hs : ((spider m).neighborFinset v).image Fin.val ⊆ candidates := by
    intro i hi
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hi
    have hadj := (spider m).mem_neighborFinset v w |>.mp hw
    simp only [spider, SimpleGraph.fromRel_adj, root, Fin.ext_iff, Fin.val_zero] at hadj
    by_cases hv : v.val = 0
    · simp only [candidates, if_pos hv, Finset.mem_insert, Finset.mem_singleton]
      omega
    · simp only [candidates, if_neg hv, Finset.mem_insert, Finset.mem_singleton]
      omega
  calc
    (spider m).degree v = ((spider m).neighborFinset v).card := rfl
    _ = (((spider m).neighborFinset v).image Fin.val).card :=
      (Finset.card_image_of_injective _ Fin.val_injective).symm
    _ ≤ candidates.card := Finset.card_le_card hs
    _ ≤ 3 := by dsimp [candidates]; split_ifs <;> exact Finset.card_le_three

/-!
## Definition 2 and arm-sum notation

Set up path prefixes, state-dependent effectiveness, and the prefix and suffix masses used by the barriers.
-/

/-- The path prefix P_j. Even when `j > m`, it contains only vertices of the long arm. -/
def pathPrefix (m j : ℕ) : Finset (Vertex m) :=
  Finset.univ.filter fun v => v.val ≤ j ∧ v.val ≤ m

/-- Definition 2: effectiveness means changing the current state.
It depends on that state, not just on the cardinality of the selected set. -/
def Effective {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) (w : State V) : Prop := average S w ≠ w

/-- The paper's prefix sum X_k; indices beyond the arm are truncated to the available vertices. -/
noncomputable def prefixMass (m k : ℕ) (w : State (Vertex m)) : ℝ :=
  ∑ v ∈ Finset.univ.filter (fun v : Vertex m => v.val < k ∧ v.val ≤ m), w v

/-- The paper's tail sum Y_t over the last `t` long-arm vertices, truncated when necessary. -/
noncomputable def suffixMass (m t : ℕ) (w : State (Vertex m)) : ℝ :=
  ∑ v ∈ Finset.univ.filter (fun v : Vertex m => m + 1 - t ≤ v.val ∧ v.val ≤ m), w v

/-!
## Reference construction and Definition 4: reachable profiles

Separate the move list constructing the profile from the resulting state and its least realization length.
-/

/-- Section 3: the chronological sequence constructing p_m from unit mass at the root.
The forward witness in S04_Main reverses this sequence of moves. -/
def referenceStrategy (m : ℕ) : Strategy (Vertex m) :=
  [pathPrefix m m, insert (leafB m) (pathPrefix m (m - 1)),
    insert (leafC m) (pathPrefix m (m - 1))] ++
  ((List.range (m - 1)).reverse.map fun j =>
    insert (if Even (m - j) then leafB m else leafC m) (pathPrefix m j))

/-- The state p_m obtained by executing `referenceStrategy m` from unit mass at the root. This is a vector, not a move list. -/
noncomputable def referenceProfile (m : ℕ) : State (Vertex m) :=
  run (referenceStrategy m) (pointMass (root m))

/-- Definition 4: profiles reachable in at most `k` moves, using Paper 1's horizon definition. -/
def profilesWithin (m k : ℕ) : Set (State (Vertex m)) :=
  horizonStates (spider m) (pointMass (root m)) k

/-- All profiles finitely reachable from root unit mass, without taking a closure. -/
def reachableProfiles (m : ℕ) : Set (State (Vertex m)) :=
  reachableSet (spider m) (pointMass (root m))

/-- The least realization length of an already reachable profile.
The reachability argument supplies existence of a realizing strategy. -/
noncomputable def profileLength (m : ℕ) (q : State (Vertex m))
    (hq : q ∈ reachableProfiles m) : ℕ := by
  classical
  exact Nat.find (show ∃ k, ∃ σ, IsLegal (spider m) σ ∧ σ.length = k ∧
      run σ (pointMass (root m)) = q from by
    obtain ⟨σ, hσ, hval⟩ := hq
    exact ⟨σ.length, σ, hσ, rfl, hval⟩)

/-!
## Specification lemmas and legality of the reference construction

Validate the minimum-length definition and the explicit reference strategy used by the later theorems.
-/

theorem profileLength_spec (m : ℕ) (q : State (Vertex m))
    (hq : q ∈ reachableProfiles m) :
    ∃ σ, IsLegal (spider m) σ ∧ σ.length = profileLength m q hq ∧
      run σ (pointMass (root m)) = q := by
  classical
  unfold profileLength
  exact Nat.find_spec (p := fun k => ∃ σ, IsLegal (spider m) σ ∧
    σ.length = k ∧ run σ (pointMass (root m)) = q) _

theorem profileLength_le (m : ℕ) (q : State (Vertex m))
    (hq : q ∈ reachableProfiles m) (σ : Strategy (Vertex m))
    (hσ : IsLegal (spider m) σ) (hval : run σ (pointMass (root m)) = q) :
    profileLength m q hq ≤ σ.length := by
  classical
  exact Nat.find_min' _ ⟨σ, hσ, rfl, hval⟩

theorem referenceStrategy_length (m : ℕ) (hm : 2 ≤ m) :
    (referenceStrategy m).length = m + 2 := by
  simp only [referenceStrategy, List.length_append, List.length_cons, List.length_nil,
    List.length_map, List.length_reverse, List.length_range]
  omega

private theorem referenceProfile_nonnegative (m : ℕ) : Nonnegative (referenceProfile m) := by
  simpa [referenceProfile, reverseProfile] using
    reverseProfile_nonnegative (referenceStrategy m).reverse (root m)

private theorem referenceProfile_mass (m : ℕ) : mass (referenceProfile m) = 1 := by
  simpa [referenceProfile, reverseProfile] using
    reverseProfile_mass (referenceStrategy m).reverse (root m)

private theorem legal_insert_neighbor {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (u v : V)
    (hS : IsLegalMove G S) (hu : u ∈ S) (huv : G.Adj u v) :
    IsLegalMove G (insert v S) := by
  refine ⟨⟨v, Finset.mem_insert_self _ _⟩, ?_⟩
  have heq : ((insert v S : Finset V) : Set V) = (S : Set V) ∪ {u, v} := by
    ext x; simp; aesop
  rw [heq]
  exact SimpleGraph.induce_union_connected hS.2.preconnected
    (SimpleGraph.induce_pair_connected_of_adj huv).preconnected ⟨u, hu, by simp⟩

private theorem pathPrefix_legal (m j : ℕ) (hj : j ≤ m) :
    IsLegalMove (spider m) (pathPrefix m j) := by
  induction j with
  | zero =>
    have heq : pathPrefix m 0 = {root m} := by
      ext v
      simp only [pathPrefix, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton, root, Fin.ext_iff, Fin.val_zero]
      omega
    rw [heq]
    refine ⟨Finset.singleton_nonempty _, ?_⟩
    rw [Finset.coe_singleton]
    exact SimpleGraph.Connected.of_subsingleton
  | succ j ih =>
    let u : Vertex m := ⟨j, by omega⟩
    let v : Vertex m := ⟨j + 1, by omega⟩
    have heq : pathPrefix m (j + 1) = insert v (pathPrefix m j) := by
      ext x
      simp only [pathPrefix, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Fin.ext_iff]
      dsimp [v]; omega
    rw [heq]
    apply legal_insert_neighbor _ _ u v (ih (by omega))
    · simp [pathPrefix, u]; omega
    · rw [spider, SimpleGraph.fromRel_adj]
      refine ⟨?_, Or.inl (Or.inl ⟨by dsimp [u]; omega, rfl⟩)⟩
      intro heq
      have := congrArg Fin.val heq
      dsimp [u, v] at this
      omega

private theorem pathPrefix_leaf_legal (m j : ℕ) (hj : j ≤ m) (v : Vertex m)
    (hv : m < v.val) : IsLegalMove (spider m) (insert v (pathPrefix m j)) := by
  apply legal_insert_neighbor _ _ (root m) v (pathPrefix_legal m j hj)
  · simp [pathPrefix, root]
  · rw [spider, SimpleGraph.fromRel_adj]
    refine ⟨?_, Or.inl (Or.inr ⟨rfl, hv⟩)⟩
    intro heq
    have := congrArg Fin.val heq
    simp only [root, Fin.val_zero] at this
    omega

/-- Every set in the reference strategy is nonempty and induces a connected subgraph. -/
theorem referenceStrategy_legal (m : ℕ) (hm : 2 ≤ m) :
    IsLegal (spider m) (referenceStrategy m) := by
  intro S hS
  simp only [referenceStrategy, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hS
  rcases hS with (rfl | rfl | rfl) | hS
  · exact pathPrefix_legal m m le_rfl
  · exact pathPrefix_leaf_legal m (m - 1) (by omega) (leafB m) (by simp [leafB])
  · exact pathPrefix_leaf_legal m (m - 1) (by omega) (leafC m) (by simp [leafC])
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hS
    have hj' := List.mem_range.mp (List.mem_reverse.mp hj)
    apply pathPrefix_leaf_legal m j (by omega)
    split_ifs <;> simp [leafB, leafC]

private theorem referenceProfile_mem (m : ℕ) (hm : 2 ≤ m) :
    referenceProfile m ∈ profilesWithin m (m + 2) := by
  exact ⟨referenceStrategy m, referenceStrategy_legal m hm,
    (referenceStrategy_length m hm).le, rfl⟩

end WaterTransport.Paper2
