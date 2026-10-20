import WaterTransport1.S03_Analysis
import Mathlib.Order.Zorn

/-!
# Paper 1: continuity and existence of an optimal finite strategy

Main results: Lemma 2.3, Theorem 2.1, and Corollary 2.1.
The optimal value is initially a supremum; attainment is proved later.
Continuity is required only on the nonnegative cone, matching the paper's domain.
Theorems using the supremum first establish nonemptiness and boundedness.

Proof route: uniform nonexpansiveness gives continuity of the value function;
cofinal sequences give upper bounds for reachability chains; a strict successor
argument forces a Zorn maximal element to attain the objective supremum.
-/

namespace WaterTransport

open Filter Topology

variable {V : Type*} [Fintype V] [DecidableEq V]

/-!
## Definitions and boundedness of optimal values

Define the supremum before proving that a reachable state attains it.
-/

/-- Objective values on all finitely reachable states, for a coordinate or a general function. -/
private def objectiveValues (G : SimpleGraph V) (f : State V → ℝ) (w : State V) : Set ℝ :=
  f '' reachableSet G w

/-- The paper's optimal-value supremum `f_sup`. -/
noncomputable def optimalValue (G : SimpleGraph V) (f : State V → ℝ) (w : State V) : ℝ :=
  sSup (objectiveValues G f w)

/-- The supremum of the water level at a fixed target vertex. -/
noncomputable def targetSup (G : SimpleGraph V) (w : State V) (x : V) : ℝ :=
  optimalValue G (fun u => u x) w

private theorem objectiveValues_nonempty (G : SimpleGraph V) (f : State V → ℝ) (w : State V) :
    (objectiveValues G f w).Nonempty :=
  ⟨f w, w, reachable_refl G w, rfl⟩

/-- Compactness of the nonnegative mass simplex bounds objective values before attainment is known. -/
private theorem objectiveValues_bddAbove (G : SimpleGraph V) (f : State V → ℝ)
    (hf : ContinuousOn f {u | Nonnegative u}) (w : State V) (hw : Nonnegative w) :
    BddAbove (objectiveValues G f w) := by
  have hcompact := (massSimplex_isCompact (V := V) (mass w)).bddAbove_image
    (hf.mono (fun _ hu => hu.1))
  apply hcompact.mono
  rintro _ ⟨u, hu, rfl⟩
  exact ⟨u, reachable_mem_massSimplex hw hu, rfl⟩

/-!
## Lemma 2.3: continuity of the optimal-value function

Use uniform continuity on a compact box together with a Lipschitz bound common to every strategy.
-/

/-- Lemma 2.3: continuity on the nonnegative cone.
Uniform nonexpansiveness supplies the upper as well as the lower continuity estimate. -/
theorem optimalValue_continuousOn (G : SimpleGraph V) (f : State V → ℝ)
    (hf : ContinuousOn f {u | Nonnegative u}) :
    ContinuousOn (optimalValue G f) {u | Nonnegative u} := by
  apply Metric.continuousOn_iff.mpr
  intro w hw ε hε
  let M := ‖w‖ + 1
  let K : Set (State V) := Set.Icc 0 (fun _ => M)
  have hK : IsCompact K := isCompact_Icc
  have hsub : K ⊆ {u | Nonnegative u} := fun _ hu => hu.1
  have hnear : ∀ a : State V, Nonnegative a → dist a w < 1 → a ∈ K := by
    intro a ha hdist
    refine ⟨ha, fun v => ?_⟩
    have hdiff : |a v - w v| ≤ dist a w := by
      simpa only [dist_eq_norm, Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (a - w) v
    have hwv : w v ≤ ‖w‖ := (le_abs_self _).trans (norm_le_pi_norm w v)
    have habs := le_abs_self (a v - w v)
    change a v ≤ ‖w‖ + 1
    linarith
  have hrun : ∀ σ : Strategy V, ∀ a ∈ K, run σ a ∈ K := by
    intro σ
    induction σ with
    | nil => intro a ha; exact ha
    | cons S σ ih =>
      intro a ha
      have hb := average_bounds S a 0 M (fun v => ⟨ha.1 v, ha.2 v⟩)
      exact ih _ ⟨fun v => (hb v).1, fun v => (hb v).2⟩
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous (hf.mono hsub)) (ε / 2) (by linarith)
  refine ⟨min 1 δ, lt_min zero_lt_one hδ, ?_⟩
  intro a ha hdist
  have hclose : ∀ σ : Strategy V, |f (run σ a) - f (run σ w)| < ε / 2 := by
    intro σ
    have hdist' : dist (run σ a) (run σ w) < δ :=
      ((run_lipschitz σ).dist_le_mul a w).trans_lt (by simpa using hdist.trans_le (min_le_right 1 δ))
    exact (Real.dist_eq _ _).symm ▸ hmod _ (hrun σ a (hnear a ha (hdist.trans_le (min_le_left 1 δ))))
      _ (hrun σ w (hnear w hw (by simp))) hdist'
  have hupper : optimalValue G f a ≤ optimalValue G f w + ε / 2 := by
    apply csSup_le (objectiveValues_nonempty G f a)
    rintro _ ⟨u, ⟨σ, hσ, rfl⟩, rfl⟩
    have hv : f (run σ w) ≤ optimalValue G f w :=
      le_csSup (objectiveValues_bddAbove G f hf w hw) ⟨run σ w, ⟨σ, hσ, rfl⟩, rfl⟩
    have hd := (abs_lt.mp (hclose σ)).2
    linarith
  have hlower : optimalValue G f w ≤ optimalValue G f a + ε / 2 := by
    apply csSup_le (objectiveValues_nonempty G f w)
    rintro _ ⟨u, ⟨σ, hσ, rfl⟩, rfl⟩
    have hv : f (run σ a) ≤ optimalValue G f a :=
      le_csSup (objectiveValues_bddAbove G f hf a ha) ⟨run σ a, ⟨σ, hσ, rfl⟩, rfl⟩
    have hd := (abs_lt.mp (hclose σ)).1
    linarith
  rw [Real.dist_eq]
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-!
## Preparation for Zorn: chains and strict successors

Work in the reachable level set preserving the initial supremum; show chains have upper bounds and nonoptimal states have successors.
-/

/-- The set `W` of reachable states preserving the initial optimal value; it contains the initial state. -/
private def optimalLevelSet (G : SimpleGraph V) (f : State V → ℝ) (w : State V) : Set (State V) :=
  {u | Reachable G w u ∧ optimalValue G f u = optimalValue G f w}

/-- A nonempty reachability chain has an increasing cofinal sequence.
Countability alone gives an enumeration; monotonicity is established separately. -/
private theorem chain_has_cofinal_sequence (G : SimpleGraph V) (w : State V)
    (c : Set (State V)) (hne : c.Nonempty) (hsub : c ⊆ reachableSet G w)
    (hc : IsChain (Reachable G) c) :
    ∃ u : ℕ → State V, (∀ n, u n ∈ c) ∧
      (∀ n, Reachable G (u n) (u (n + 1))) ∧
      ∀ z ∈ c, ∃ n, Reachable G z (u n) := by
  classical
  obtain ⟨f, hf⟩ := ((reachableSet_countable G w).mono hsub).exists_surjective hne
  let chooseMax : c → c → c := fun a b => if Reachable G a.val b.val then b else a
  have hleft : ∀ a b : c, Reachable G a.val (chooseMax a b).val := by
    intro a b
    dsimp [chooseMax]
    split_ifs with h
    · exact h
    · exact reachable_refl G a.val
  have hright : ∀ a b : c, Reachable G b.val (chooseMax a b).val := by
    intro a b
    dsimp [chooseMax]
    split_ifs with h
    · exact reachable_refl G b.val
    · by_cases he : a.val = b.val
      · exact he ▸ reachable_refl G a.val
      · exact (hc a.property b.property he).resolve_left h
  let seq : ℕ → c := fun n => Nat.rec (f 0) (fun k a => chooseMax a (f (k + 1))) n
  have henum : ∀ n, Reachable G (f n).val (seq n).val := by
    intro n
    cases n with
    | zero => exact reachable_refl G (f 0).val
    | succ n => exact hright (seq n) (f (n + 1))
  refine ⟨fun n => (seq n).val, fun n => (seq n).property,
    fun n => hleft (seq n) (f (n + 1)), ?_⟩
  intro z hz
  obtain ⟨n, hn⟩ := hf ⟨z, hz⟩
  exact ⟨n, by simpa only [hn] using henum n⟩

/-- Lemmas 2.2 and 2.3 give every chain in `W` an upper bound still in `W`. -/
private theorem optimalLevelSet_chain_upperBound (G : SimpleGraph V) (f : State V → ℝ)
    (hf : ContinuousOn f {u | Nonnegative u}) (w : State V) (hw : Nonnegative w)
    (c : Set (State V)) (hsub : c ⊆ optimalLevelSet G f w)
    (hc : IsChain (Reachable G) c) :
    ∃ u ∈ optimalLevelSet G f w, ∀ z ∈ c, Reachable G z u := by
  by_cases hne : c.Nonempty
  · obtain ⟨u, hu, hstep, hcofinal⟩ := chain_has_cofinal_sequence G w c hne
      (fun z hz => (hsub hz).1) hc
    obtain ⟨z, hz, hlim, hreach⟩ := reachable_sequence_converges G u
      (reachable_nonnegative hw (hsub (hu 0)).1) hstep
    have hwithin : Tendsto u atTop (𝓝[{u | Nonnegative u}] z) :=
      tendsto_nhdsWithin_iff.mpr ⟨hlim, Filter.Eventually.of_forall
        (fun n => reachable_nonnegative hw (hsub (hu n)).1)⟩
    have hvalue := ((optimalValue_continuousOn G f hf) z hz).tendsto.comp hwithin
    have hconst : Tendsto (fun n => optimalValue G f (u n)) atTop
        (𝓝 (optimalValue G f w)) := by
      have heq : (fun n => optimalValue G f (u n)) = fun _ : ℕ => optimalValue G f w :=
        funext (fun n => (hsub (hu n)).2)
      rw [heq]
      exact tendsto_const_nhds
    refine ⟨z, ⟨reachable_trans (hsub (hu 0)).1 (hreach 0),
      tendsto_nhds_unique hvalue hconst⟩, ?_⟩
    intro a ha
    obtain ⟨n, hn⟩ := hcofinal a ha
    exact reachable_trans hn (hreach n)
  · refine ⟨w, ⟨reachable_refl G w, rfl⟩, ?_⟩
    intro z hz
    exact (hne ⟨z, hz⟩).elim

/-- Reachability restricts the set of future competitors, so the optimal value cannot increase. -/
private theorem optimalValue_le_of_reachable (G : SimpleGraph V) (f : State V → ℝ)
    (hf : ContinuousOn f {u | Nonnegative u}) (w u : State V) (hw : Nonnegative w)
    (hu : Reachable G w u) : optimalValue G f u ≤ optimalValue G f w := by
  apply csSup_le (objectiveValues_nonempty G f u)
  rintro _ ⟨z, hz, rfl⟩
  exact le_csSup (objectiveValues_bddAbove G f hf w hw) ⟨z, reachable_trans hu hz, rfl⟩

/-- A finite-branching Bellman step: before the supremum is attained, some one-step
successor changes the state strictly while preserving the optimal value. -/
private theorem exists_optimalLevel_successor (G : SimpleGraph V) (f : State V → ℝ)
    (hf : ContinuousOn f {u | Nonnegative u}) (w : State V) (hw : Nonnegative w)
    (hgap : f w < optimalValue G f w) :
    ∃ S, IsLegalMove G S ∧ average S w ≠ w ∧
      optimalValue G f (average S w) = optimalValue G f w := by
  classical
  let moves : Finset (Finset V) := Finset.univ.filter (fun S => IsLegalMove G S ∧ average S w ≠ w)
  let vals := insert (f w) (moves.image (fun S => optimalValue G f (average S w)))
  let b := sSup (vals : Set ℝ)
  have hbase : f w ≤ b := le_csSup vals.finite_toSet.bddAbove (by simp [vals])
  have hbranch : ∀ S, IsLegalMove G S → average S w ≠ w → optimalValue G f (average S w) ≤ b := by
    intro S hS hne
    apply le_csSup vals.finite_toSet.bddAbove
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨S, by simp [moves, hS, hne], rfl⟩
  have hbound : ∀ σ, IsLegal G σ → f (run σ w) ≤ b := by
    intro σ
    induction σ with
    | nil => intro _; exact hbase
    | cons S σ ih =>
      intro hlegal
      obtain ⟨hS, hσ⟩ := (isLegal_cons G S σ).mp hlegal
      by_cases hfix : average S w = w
      · simpa only [run_cons, hfix] using ih hσ
      · exact (le_csSup (objectiveValues_bddAbove G f hf _ (average_nonnegative S hw))
          ⟨run σ (average S w), ⟨σ, hσ, rfl⟩, rfl⟩).trans (hbranch S hS hfix)
  have hsup : optimalValue G f w ≤ b := by
    apply csSup_le (objectiveValues_nonempty G f w)
    rintro _ ⟨u, ⟨σ, hσ, rfl⟩, rfl⟩
    exact hbound σ hσ
  have hbmem : b ∈ vals := Finset.Nonempty.csSup_mem ⟨f w, by simp [vals]⟩
  rcases Finset.mem_insert.mp hbmem with hb | hb
  · exact (not_lt_of_ge (hsup.trans_eq hb) hgap).elim
  · obtain ⟨S, hSmem, hval⟩ := Finset.mem_image.mp hb
    have hS := (Finset.mem_filter.mp hSmem).2
    refine ⟨S, hS.1, hS.2, le_antisymm ?_ (hsup.trans_eq hval.symm)⟩
    exact optimalValue_le_of_reachable G f hf w (average S w) hw
      (oneStep_reachable ⟨S, hS.1, rfl⟩)

/-!
## Theorem 2.1 and Corollary 2.1: finite optimal strategies exist

Apply Zorn, then specialize a continuous objective to a single target coordinate.
-/

/-- Theorem 2.1: every objective continuous on the nonnegative cone attains its
maximum at a finitely reachable state. The finite graph may be disconnected or empty. -/
theorem continuous_objective_attained (G : SimpleGraph V) (f : State V → ℝ)
    (hf : ContinuousOn f {u | Nonnegative u}) (w : State V) (hw : Nonnegative w) :
    ∃ u, Reachable G w u ∧ f u = optimalValue G f w := by
  -- Use reachability only on W; preserve the function space's existing pointwise order.
  let W := {u // u ∈ optimalLevelSet G f w}
  let r : W → W → Prop := fun u v => Reachable G u.val v.val
  have hbound : ∀ c : Set W, IsChain r c → ∃ ub : W, ∀ a ∈ c, r a ub := by
    intro c hc
    have hsub : Subtype.val '' c ⊆ optimalLevelSet G f w := by
      rintro _ ⟨a, _, rfl⟩
      exact a.property
    have hc' : IsChain (Reachable G) (Subtype.val '' c) :=
      IsChain.image_of_map_rel r (Reachable G) Subtype.val (fun _ _ h => h) hc
    obtain ⟨u, hu, hub⟩ := optimalLevelSet_chain_upperBound G f hf w hw _ hsub hc'
    exact ⟨⟨u, hu⟩, fun a ha => hub a.val ⟨a, ha, rfl⟩⟩
  obtain ⟨m, hm⟩ := exists_maximal_of_chains_bounded hbound
    (fun h₁ h₂ => reachable_trans h₁ h₂)
  have hmnonneg : Nonnegative m.val := reachable_nonnegative hw m.property.1
  have hle : f m.val ≤ optimalValue G f m.val :=
    le_csSup (objectiveValues_bddAbove G f hf m.val hmnonneg)
      ⟨m.val, reachable_refl G m.val, rfl⟩
  have heq : f m.val = optimalValue G f m.val := by
    by_contra hne
    obtain ⟨S, hS, hchange, hlevel⟩ :=
      exists_optimalLevel_successor G f hf m.val hmnonneg (lt_of_le_of_ne hle hne)
    have hstep : Reachable G m.val (average S m.val) := oneStep_reachable ⟨S, hS, rfl⟩
    let a : W := ⟨average S m.val,
      reachable_trans m.property.1 hstep, hlevel.trans m.property.2⟩
    exact hchange (reachable_antisymm (hm a hstep) hstep)
  exact ⟨m.val, m.property.1, heq.trans m.property.2⟩

/-- Strategy form of Theorem 2.1: an arbitrary continuous objective has a finite global optimizer. -/
theorem exists_optimalFor (G : SimpleGraph V) (f : State V → ℝ)
    (hf : ContinuousOn f {u | Nonnegative u}) (w : State V) (hw : Nonnegative w) :
    ∃ σ, IsOptimalFor G f w σ := by
  obtain ⟨u, ⟨σ, hσ, rfl⟩, hmax⟩ := continuous_objective_attained G f hf w hw
  refine ⟨σ, hσ, ?_⟩
  intro τ hτ
  rw [hmax]
  exact le_csSup (objectiveValues_bddAbove G f hf w hw)
    ⟨run τ w, ⟨τ, hτ, rfl⟩, rfl⟩

/-- Corollary 2.1: a finite legal strategy attains the maximum level at a prescribed target. -/
theorem target_attained (G : SimpleGraph V) (w : State V) (hw : Nonnegative w) (x : V) :
    ∃ σ, IsLegal G σ ∧ run σ w x = targetSup G w x := by
  obtain ⟨u, ⟨σ, hσ, hrun⟩, hu⟩ :=
    continuous_objective_attained G (fun u => u x) (continuous_apply x).continuousOn w hw
  exact ⟨σ, hσ, by simpa only [hrun, targetSup] using hu⟩

/-- Strategy form of Corollary 2.1, supplying the existence needed for `optimalLength`. -/
theorem exists_optimal (G : SimpleGraph V) (w : State V) (hw : Nonnegative w) (x : V) :
    ∃ σ, IsOptimal G w x σ :=
  exists_optimalFor G (fun u => u x) (continuous_apply x).continuousOn w hw

/-- Global domination of all strategies is equivalent to attaining the target supremum. -/
theorem isOptimal_iff_attains (G : SimpleGraph V) (w : State V) (hw : Nonnegative w)
    (x : V) (σ : Strategy V) :
    IsOptimal G w x σ ↔ IsLegal G σ ∧ run σ w x = targetSup G w x := by
  have hb := objectiveValues_bddAbove G (fun u => u x) (continuous_apply x).continuousOn w hw
  constructor
  · intro h
    refine ⟨h.1, le_antisymm (le_csSup hb ⟨run σ w, ⟨σ, h.1, rfl⟩, rfl⟩) ?_⟩
    apply csSup_le (objectiveValues_nonempty G (fun u => u x) w)
    rintro _ ⟨u, ⟨τ, hτ, rfl⟩, rfl⟩
    exact h.2 τ hτ
  · rintro ⟨hlegal, hval⟩
    refine ⟨hlegal, fun τ hτ => ?_⟩
    change run τ w x ≤ run σ w x
    rw [hval]
    exact le_csSup hb ⟨run τ w, ⟨τ, hτ, rfl⟩, rfl⟩

end WaterTransport
