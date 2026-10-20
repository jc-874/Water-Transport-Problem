import WaterTransport1.S07_PathShortening
import Mathlib.Data.Fin.Rev

/-!
# Paper 1: path theorems and finite-horizon stabilization

S07_PathShortening proves the core two-step result using general attainment and
a shortest optimal strategy. This file presents the public conclusions:
two-step domination, stabilization, Lemma 3.1, and Theorem 3.1.
-/

namespace WaterTransport

variable {n : ℕ}

/-!
## Two-step strategies and stabilization

Expose domination and attainment consequences of the core shortening theorem.
-/

/-- Finite-horizon shortening interface. A globally optimal two-step strategy dominates
the given strategy; the retained horizon assumption ensures two steps fit the new bound. -/
private theorem path_horizon_shortening (w : State (Fin n)) (hw : Nonnegative w) (x : Fin n)
    (t : ℕ) (ht : 2 ≤ t) (σ : Strategy (Fin n))
    (hσ : IsLegal (SimpleGraph.pathGraph n) σ) (hlen : σ.length ≤ t + 1) :
    ∃ τ, IsLegal (SimpleGraph.pathGraph n) τ ∧ τ.length ≤ t ∧ run σ w x ≤ run τ w x := by
  clear hlen
  obtain ⟨τ, hτ, hτlen⟩ := path_two_step_core w hw x
  exact ⟨τ, hτ.1, hτlen.trans ht, hτ.2 σ hσ⟩

/-- Every finite legal strategy is dominated by some strategy of length at most two. -/
theorem path_two_step_dominates (w : State (Fin n)) (hw : Nonnegative w) (x : Fin n)
    (σ : Strategy (Fin n)) (hσ : IsLegal (SimpleGraph.pathGraph n) σ) :
    ∃ τ, IsLegal (SimpleGraph.pathGraph n) τ ∧ τ.length ≤ 2 ∧ run σ w x ≤ run τ w x := by
  obtain ⟨τ, hτ, hτlen⟩ := path_two_step_core w hw x
  exact ⟨τ, hτ.1, hτlen, hτ.2 σ hσ⟩

/-- An optimal strategy of length at most two, obtained from the shortest-strategy argument. -/
theorem path_exists_optimal_two (w : State (Fin n)) (hw : Nonnegative w) (x : Fin n) :
    ∃ σ, IsOptimal (SimpleGraph.pathGraph n) w x σ ∧ σ.length ≤ 2 := by
  exact path_two_step_core w hw x

/-- End of Section 3: consecutive horizon maxima agree once the horizon is at least two. -/
theorem path_horizon_stabilizes (w : State (Fin n)) (hw : Nonnegative w) (x : Fin n)
    (t : ℕ) (ht : 2 ≤ t) :
    horizonMax (SimpleGraph.pathGraph n) w x t =
      horizonMax (SimpleGraph.pathGraph n) w x (t + 1) := by
  apply le_antisymm (horizonMax_mono _ w x (Nat.le_succ t))
  apply horizonMax_le
  intro σ hσ hlen
  obtain ⟨τ, hτ, hτlen, hdom⟩ := path_horizon_shortening w hw x t ht σ hσ hlen
  exact hdom.trans (le_horizonMax _ w x t τ hτ hτlen)

/-!
## Lemma 3.1: the two endpoints

Use the prefix bound for the left endpoint and reflection for the right endpoint.
-/

/-- Lemma 3.1 for the left endpoint: one move suffices. -/
theorem endpoint_optimalLength_le_one (w : State (Fin (n + 1))) (hw : Nonnegative w) :
    optimalLength (SimpleGraph.pathGraph (n + 1)) w hw 0 ≤ 1 := by
  obtain ⟨b, hb⟩ := endpoint_prefix_dominates w hw
  have h0b : (0 : Fin (n + 1)) ≤ b := Fin.zero_le b
  apply (optimalLength_le_iff _ w hw 0 1).mpr
  refine ⟨[pathInterval 0 b], ⟨?_, ?_⟩, by simp⟩
  · simpa using pathInterval_legal 0 b h0b
  · intro σ hσ
    change run σ w 0 ≤ average (pathInterval 0 b) w 0
    rw [average_apply_mem (pathInterval 0 b) w (Finset.mem_Icc.mpr ⟨le_rfl, h0b⟩)]
    exact hb σ hσ

/-- Lemma 3.1 for the right endpoint, by reflecting and transporting the optimal strategy. -/
theorem rightEndpoint_optimalLength_le_one (w : State (Fin (n + 1))) (hw : Nonnegative w) :
    optimalLength (SimpleGraph.pathGraph (n + 1)) w hw (Fin.last n) ≤ 1 := by
  let e := pathReflection (n + 1)
  have hnon : Nonnegative (w ∘ e) := fun v => hw (e v)
  obtain ⟨σ, hσ, hlen⟩ := (optimalLength_le_iff _ (w ∘ e) hnon 0 1).mp
    (endpoint_optimalLength_le_one (w ∘ e) hnon)
  have hopt := hσ.map_iso e
  have hstate : (w ∘ e) ∘ e.symm = w := by funext v; simp
  have hx : e 0 = Fin.last n := by apply Fin.ext; simp [e, pathReflection, Fin.revPerm]
  rw [hstate, hx] at hopt
  apply (optimalLength_le_iff _ w hw (Fin.last n) 1).mpr
  exact ⟨_, hopt, by simpa using hlen⟩

/-!
## Theorem 3.1: length, supremum, and isomorphism formulations

Present equivalent interfaces for later examples and for paths with arbitrary vertex labels.
-/

/-- Theorem 3.1: the shortest globally optimal length on a path is at most two. -/
theorem path_optimalLength_le_two (w : State (Fin n)) (hw : Nonnegative w) (x : Fin n) :
    optimalLength (SimpleGraph.pathGraph n) w hw x ≤ 2 :=
  (optimalLength_le_iff _ w hw x 2).mpr (path_exists_optimal_two w hw x)

/-- A globally optimal strategy of length at least three has a shorter globally optimal replacement. -/
private theorem shorten_path_optimal (w : State (Fin n)) (hw : Nonnegative w) (x : Fin n)
    (σ : Strategy (Fin n)) (hopt : IsOptimal (SimpleGraph.pathGraph n) w x σ)
    (hlen : 3 ≤ σ.length) :
    ∃ τ, IsOptimal (SimpleGraph.pathGraph n) w x τ ∧ τ.length < σ.length := by
  obtain ⟨τ, hτ, hτlen, hdom⟩ := path_two_step_dominates w hw x σ hopt.1
  exact ⟨τ, ⟨hτ, fun ρ hρ => (hopt.2 ρ hρ).trans hdom⟩, by omega⟩

/-- The two-step finite maximum equals the supremum over all finite legal strategies. -/
theorem path_targetSup_eq_horizon_two (w : State (Fin n)) (hw : Nonnegative w) (x : Fin n) :
    targetSup (SimpleGraph.pathGraph n) w x = horizonMax (SimpleGraph.pathGraph n) w x 2 := by
  obtain ⟨σ, hσ, hlen⟩ := path_exists_optimal_two w hw x
  rw [← ((isOptimal_iff_attains _ w hw x σ).mp hσ).2]
  apply le_antisymm (le_horizonMax _ w x 2 σ hσ.1 hlen)
  exact horizonMax_le _ w x 2 _ (fun τ hτ _ => hσ.2 τ hτ)

/-- The path length bound transported through a graph isomorphism to any vertex labelling. -/
theorem path_optimalLength_le_two_of_iso {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (e : G ≃g SimpleGraph.pathGraph n)
    (w : State V) (hw : Nonnegative w) (x : V) :
    optimalLength G w hw x ≤ 2 := by
  obtain ⟨σ, hσ, hlen⟩ := path_exists_optimal_two (w ∘ e.symm)
    (fun v => hw (e.symm v)) (e x)
  have hopt := hσ.map_iso e.symm
  change IsOptimal G ((w ∘ e.symm) ∘ e) (e.symm (e x))
    (σ.map (Finset.map e.symm.toEquiv.toEmbedding)) at hopt
  have hstate : (w ∘ e.symm) ∘ e = w := by funext v; simp
  rw [hstate, e.symm_apply_apply] at hopt
  apply (optimalLength_le_iff G w hw x 2).mpr
  exact ⟨_, hopt, by simpa using hlen⟩

end WaterTransport
