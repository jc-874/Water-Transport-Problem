import WaterTransport1.S04_Existence

/-!
# Paper 1, Definition 3.1: the shortest optimal length

`optimalLength` is the least natural-number length of a globally optimal strategy.
Corollary 2.1 supplies existence before this minimum is defined. The nonnegativity
argument records the domain on which that existence theorem applies.

Reading order: define the minimum and its specification; characterize length
bounds; prove two general redundancy facts for a shortest optimal strategy.
-/

namespace WaterTransport

variable {V : Type*} [Fintype V] [DecidableEq V]

/-!
## Definition 3.1 and the minimum-length interface

Establish existence, define the natural-number minimum, and characterize its upper bounds.
-/

private theorem exists_optimal_length (G : SimpleGraph V) (w : State V)
    (hw : Nonnegative w) (x : V) :
    ∃ k : ℕ, ∃ σ : Strategy V, IsOptimal G w x σ ∧ σ.length = k := by
  obtain ⟨σ, hσ⟩ := exists_optimal G w hw x
  exact ⟨σ.length, σ, hσ, rfl⟩

/-- The paper's `t(G,x,w)`, with value zero when doing nothing is already optimal. -/
noncomputable def optimalLength (G : SimpleGraph V) (w : State V)
    (hw : Nonnegative w) (x : V) : ℕ := by
  classical
  exact Nat.find (exists_optimal_length G w hw x)

/-- A legal globally optimal strategy realizes the minimum length. -/
theorem optimalLength_spec (G : SimpleGraph V) (w : State V)
    (hw : Nonnegative w) (x : V) :
    ∃ σ, IsOptimal G w x σ ∧ σ.length = optimalLength G w hw x := by
  classical
  exact Nat.find_spec (exists_optimal_length G w hw x)

/-- Every globally optimal strategy gives an upper bound on the minimum length. -/
theorem optimalLength_le (G : SimpleGraph V) (w : State V) (hw : Nonnegative w)
    (x : V) (σ : Strategy V) (hσ : IsOptimal G w x σ) :
    optimalLength G w hw x ≤ σ.length := by
  classical
  exact Nat.find_min' (exists_optimal_length G w hw x) ⟨σ, hσ, rfl⟩

/-- A length bound holds exactly when some globally optimal strategy satisfies that bound. -/
theorem optimalLength_le_iff (G : SimpleGraph V) (w : State V) (hw : Nonnegative w)
    (x : V) (k : ℕ) :
    optimalLength G w hw x ≤ k ↔ ∃ σ, IsOptimal G w x σ ∧ σ.length ≤ k := by
  constructor
  · intro hk
    obtain ⟨σ, hσ, hlen⟩ := optimalLength_spec G w hw x
    exact ⟨σ, hσ, by simpa only [hlen] using hk⟩
  · rintro ⟨σ, hσ, hlen⟩
    exact (optimalLength_le G w hw x σ hσ).trans hlen

/-!
## Private preparation: necessary shapes of the last moves

Deletion of redundant steps constrains a shortest optimal strategy on any graph.
-/

/-- Preparation: the last move of a shortest nonempty optimal strategy contains the target. -/
private theorem shortest_last_contains_target (G : SimpleGraph V) (w : State V) (hw : Nonnegative w)
    (x : V) (σ : Strategy V) (S : Finset V)
    (hopt : IsOptimal G w x (σ ++ [S]))
    (hmin : (σ ++ [S]).length = optimalLength G w hw x) : x ∈ S := by
  by_contra hx
  have heq : run (σ ++ [S]) w x = run σ w x := by
    rw [run_append, run_singleton, average_apply_not_mem _ _ hx]
  have hσ : IsOptimal G w x σ :=
    ⟨((isLegal_append G σ [S]).mp hopt.1).1, fun τ hτ => (hopt.2 τ hτ).trans_eq heq⟩
  have hle := optimalLength_le G w hw x σ hσ
  simp only [List.length_append, List.length_singleton] at hmin
  omega

/-- Preparation: the last two moves of a shortest optimal strategy overlap and are
incomparable by inclusion. Each excluded case allows an explicit deletion of one move. -/
private theorem shortest_last_two_overlap_incomparable (G : SimpleGraph V)
    (w : State V) (hw : Nonnegative w) (x : V) (σ : Strategy V) (S T : Finset V)
    (hopt : IsOptimal G w x (σ ++ [S, T]))
    (hmin : (σ ++ [S, T]).length = optimalLength G w hw x) :
    (S ∩ T).Nonempty ∧ ¬ S ⊆ T ∧ ¬ T ⊆ S := by
  have hlegal := (isLegal_append G σ [S, T]).mp hopt.1
  have hS : IsLegalMove G S := hlegal.2 S (by simp)
  have hT : IsLegalMove G T := hlegal.2 T (by simp)
  have hx : x ∈ T := shortest_last_contains_target G w hw x (σ ++ [S]) T
    (by simpa only [List.append_assoc, List.cons_append, List.nil_append] using hopt)
    (by simpa only [List.append_assoc, List.cons_append, List.nil_append] using hmin)
  have hshort : ∀ R, IsLegalMove G R →
      run [S, T] (run σ w) x = average R (run σ w) x → False := by
    intro R hR heq
    have hopt' : IsOptimal G w x (σ ++ [R]) := by
      refine ⟨(isLegal_append G σ [R]).mpr ⟨hlegal.1, by simpa using hR⟩, ?_⟩
      intro τ hτ
      simpa only [run_append, run_singleton, heq] using hopt.2 τ hτ
    have hle := optimalLength_le G w hw x (σ ++ [R]) hopt'
    simp only [List.length_append, List.length_cons, List.length_nil] at hmin hle
    omega
  refine ⟨?_, ?_, ?_⟩
  · by_contra hne
    have hd : Disjoint S T := Finset.disjoint_iff_inter_eq_empty.mpr
      (Finset.not_nonempty_iff_eq_empty.mp hne)
    apply hshort T hT
    have hxS : x ∉ S := fun hxs => Finset.disjoint_left.mp hd hxs hx
    rw [run_cons, run_singleton, average_comm_of_disjoint T S hd.symm,
      average_apply_not_mem S _ hxS]
  · intro hST
    exact hshort T hT (congrFun (average_absorb_subset S T hST (run σ w)) x)
  · intro hTS
    exact hshort S hS (congrFun (average_subset_absorb T S hTS (run σ w)) x)

end WaterTransport
