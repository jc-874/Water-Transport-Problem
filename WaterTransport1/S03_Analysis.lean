import WaterTransport1.S02_Strategies
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Sequences

/-!
# Paper 1: analysis for Lemmas 2.2 and 2.3

The default norm on `V -> Real` is the maximum coordinate norm. Convergence is
expressed using `Tendsto`; the paper's sum of squares is the separate `energy`.

Proof route: equal-level connected components reconstruct a limit exactly;
uniform nonexpansiveness and compactness provide a limit; energy trapping makes
the whole sequence converge and makes that limit finitely reachable.
The uniform Lipschitz bound will also supply the two-sided continuity estimate
for the optimal-value function in S04_Existence.
-/

namespace WaterTransport

open Filter Topology

variable {V : Type*} [Fintype V] [DecidableEq V]

/-!
## Preparation: connected components of equal limit levels

Retain only edges with equal endpoint levels in the candidate limit.
Moves fixing that limit preserve the mass of each component. Once these masses
agree with the limit, averaging each component once reaches the limit exactly.
-/

private def levelGraph (G : SimpleGraph V) (w : State V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ w a = w b
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

private noncomputable def levelBlock {G : SimpleGraph V} {w : State V}
    (C : (levelGraph G w).ConnectedComponent) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => (levelGraph G w).connectedComponentMk v = C)

@[simp] private theorem mem_levelBlock {G : SimpleGraph V} {w : State V}
    (C : (levelGraph G w).ConnectedComponent) (v : V) :
    v ∈ levelBlock C ↔ (levelGraph G w).connectedComponentMk v = C := by
  classical
  simp [levelBlock]

private theorem levelBlock_legal {G : SimpleGraph V} {w : State V}
    (C : (levelGraph G w).ConnectedComponent) : IsLegalMove G (levelBlock C) := by
  have he : (levelBlock C : Set V) = C.supp := by
    ext v
    simp only [Finset.mem_coe, mem_levelBlock, SimpleGraph.ConnectedComponent.mem_supp_iff]
  constructor
  · obtain ⟨v, hv⟩ := C.nonempty_supp
    exact ⟨v, (mem_levelBlock C v).mpr hv⟩
  · rw [he]
    apply SimpleGraph.Connected.mono (G := (levelGraph G w).induce C.supp)
      (fun _ _ h => h.1) C.connected_toSimpleGraph

private theorem levelBlock_constant {G : SimpleGraph V} {w : State V}
    (C : (levelGraph G w).ConnectedComponent) {a b : V}
    (ha : a ∈ levelBlock C) (hb : b ∈ levelBlock C) : w a = w b := by
  have hr := C.reachable_of_mem_supp ((mem_levelBlock C a).mp ha) ((mem_levelBlock C b).mp hb)
  clear ha hb
  obtain ⟨p⟩ := hr
  induction p with
  | nil => rfl
  | cons h p ih => exact h.2.trans ih

private theorem levelBlock_disjoint {G : SimpleGraph V} {w : State V}
    {C D : (levelGraph G w).ConnectedComponent} (h : C ≠ D) :
    Disjoint (levelBlock C) (levelBlock D) := by
  apply Finset.disjoint_left.mpr
  intro v hv hv'
  exact h (((mem_levelBlock C v).mp hv).symm.trans ((mem_levelBlock D v).mp hv'))

/-- A connected averaging set fixing `w` lies in one equal-level component of `w`. -/
private theorem fixed_move_subset_levelBlock {G : SimpleGraph V} {w : State V}
    (S : Finset V) (hS : IsLegalMove G S) (hfix : average S w = w) :
    ∃ C : (levelGraph G w).ConnectedComponent, S ⊆ levelBlock C := by
  obtain ⟨a, ha⟩ := hS.1
  have he : ∀ v ∈ S, w v = mean S w := by
    intro v hv
    exact (congrFun hfix v).symm.trans (average_apply_mem S w hv)
  let φ : (G.induce (S : Set V)) →g levelGraph G w :=
    { toFun := Subtype.val
      map_rel' := fun {a b} hab => ⟨hab, (he a.val a.property).trans (he b.val b.property).symm⟩ }
  refine ⟨(levelGraph G w).connectedComponentMk a, fun v hv => ?_⟩
  apply (mem_levelBlock _ v).mpr
  exact SimpleGraph.ConnectedComponent.sound
    ((hS.2.preconnected ⟨v, hv⟩ ⟨a, ha⟩).map φ)

/-- A move inside one level component preserves the mass of every level component. -/
private theorem sum_average_levelBlock {G : SimpleGraph V} {w : State V}
    (S : Finset V) (hS : IsLegalMove G S) (hfix : average S w = w)
    (C : (levelGraph G w).ConnectedComponent) (u : State V) :
    ∑ v ∈ levelBlock C, average S u v = ∑ v ∈ levelBlock C, u v := by
  classical
  obtain ⟨D, hD⟩ := fixed_move_subset_levelBlock S hS hfix
  by_cases h : C = D
  · subst D
    exact sum_average_of_subset S (levelBlock C) hD u
  · apply Finset.sum_congr rfl
    intro v hv
    apply average_apply_not_mem
    intro hvS
    exact Finset.disjoint_left.mp (levelBlock_disjoint h) hv (hD hvS)

private theorem sum_run_levelBlock {G : SimpleGraph V} {w : State V}
    (σ : Strategy V) (hσ : IsLegal G σ) (hfix : ∀ S ∈ σ, average S w = w)
    (C : (levelGraph G w).ConnectedComponent) (u : State V) :
    ∑ v ∈ levelBlock C, run σ u v = ∑ v ∈ levelBlock C, u v := by
  induction σ generalizing u with
  | nil => rfl
  | cons S σ ih =>
    obtain ⟨hS, hσ⟩ := (isLegal_cons _ _ _).mp hσ
    rw [run_cons, ih hσ (fun T hT => hfix T (List.mem_cons_of_mem _ hT))]
    exact sum_average_levelBlock S hS (hfix S (List.mem_cons_self ..)) C u

/-- If a component has the required total mass, one average gives its prescribed limit level. -/
private theorem average_levelBlock_value {G : SimpleGraph V} {w u : State V}
    (C : (levelGraph G w).ConnectedComponent)
    (hs : ∑ v ∈ levelBlock C, u v = ∑ v ∈ levelBlock C, w v)
    {v : V} (hv : v ∈ levelBlock C) : average (levelBlock C) u v = w v := by
  rw [average_apply_mem _ _ hv, mean, hs]
  have he : ∑ z ∈ levelBlock C, w z = (levelBlock C).card * w v := by
    calc
      _ = ∑ _z ∈ levelBlock C, w v :=
        Finset.sum_congr rfl (fun z hz => levelBlock_constant C hz hv)
      _ = _ := by simp
  rw [he]
  have hc : ((levelBlock C).card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨v, hv⟩)
  exact mul_div_cancel_left₀ _ hc

/-- Average the finitely many disjoint level components to obtain the target state exactly. -/
private theorem reachable_of_levelBlock_sums (G : SimpleGraph V) (w u : State V)
    (hs : ∀ C : (levelGraph G w).ConnectedComponent,
      ∑ v ∈ levelBlock C, u v = ∑ v ∈ levelBlock C, w v) : Reachable G u w := by
  classical
  letI : Fintype (levelGraph G w).ConnectedComponent := Fintype.ofFinite _
  have hpres : ∀ (D C : (levelGraph G w).ConnectedComponent) (z : State V),
      ∑ v ∈ levelBlock C, average (levelBlock D) z v = ∑ v ∈ levelBlock C, z v := by
    intro D C z
    by_cases h : C = D
    · subst D
      exact sum_average_of_subset _ _ (Finset.Subset.refl _) z
    · apply Finset.sum_congr rfl
      intro v hv
      exact average_apply_not_mem _ _
        (fun hv' => Finset.disjoint_left.mp (levelBlock_disjoint h) hv hv')
  have hrun : ∀ (L : List (levelGraph G w).ConnectedComponent) (z : State V),
      (∀ C : (levelGraph G w).ConnectedComponent,
        ∑ v ∈ levelBlock C, z v = ∑ v ∈ levelBlock C, w v) → ∀ v,
      run (L.map levelBlock) z v =
        if (levelGraph G w).connectedComponentMk v ∈ L then w v else z v := by
    intro L
    induction L with
    | nil => intro z _ v; simp
    | cons D L ih =>
      intro z hz v
      simp only [List.map_cons, run_cons]
      rw [ih _ (fun C => (hpres D C z).trans (hz C))]
      by_cases hmem : (levelGraph G w).connectedComponentMk v ∈ L
      · simp [hmem]
      · rw [if_neg hmem]
        by_cases he : (levelGraph G w).connectedComponentMk v = D
        · simp only [List.mem_cons, he, true_or, if_true]
          exact average_levelBlock_value D (hz D) ((mem_levelBlock D v).mpr he)
        · simp only [hmem, he, List.mem_cons, false_or, if_false]
          exact average_apply_not_mem _ _ (fun hv => he ((mem_levelBlock D v).mp hv))
  let L := (Finset.univ : Finset (levelGraph G w).ConnectedComponent).toList
  refine ⟨L.map levelBlock, ?_, ?_⟩
  · intro S hS
    obtain ⟨C, _, rfl⟩ := List.mem_map.mp hS
    exact levelBlock_legal C
  · funext v
    simpa [L] using hrun L u hs v

/-!
## Analysis: nonexpansiveness, compactness, and convergence

First relate energy to the topology and obtain bounds uniform over all strategies.
Then use a compact mass simplex and a local trapping argument to prove convergence.
-/

/-- Convergence to `w` is equivalent to the energy of the difference tending to zero. -/
theorem tendsto_iff_energy_sub_tendsto_zero (u : ℕ → State V) (w : State V) :
    Tendsto u atTop (𝓝 w) ↔
      Tendsto (fun n => energy (u n - w)) atTop (𝓝 0) := by
  constructor
  · intro h
    have hv := tendsto_pi_nhds.mp h
    have hs := tendsto_finsetSum Finset.univ (fun v _ => ((hv v).sub_const (w v)).pow 2)
    simpa [energy] using hs
  · intro h
    apply tendsto_pi_nhds.mpr
    intro v
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h (ε^2) (sq_pos_of_pos hε)
    refine ⟨N, fun n hn => ?_⟩
    have hsmall := hN n hn
    have hcoord : (u n v - w v)^2 ≤ energy (u n - w) :=
      Finset.single_le_sum (fun j _ => sq_nonneg ((u n - w) j)) (Finset.mem_univ v)
    rw [Real.dist_eq, sub_zero] at hsmall
    rw [Real.dist_eq]
    have he : energy (u n - w) < ε^2 := (le_abs_self _).trans_lt hsmall
    exact abs_lt.mpr ⟨by nlinarith, by nlinarith⟩

/-- Every average is 1-Lipschitz for the maximum coordinate norm. -/
private theorem average_lipschitz (S : Finset V) : LipschitzWith 1 (average S : State V → State V) := by
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro w u
  change ‖averageLinear S w - averageLinear S u‖ ≤ (1 : ℝ) * ‖w - u‖
  rw [← map_sub, one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg (w - u))).mpr
  have hb := average_bounds S (w - u) (-‖w - u‖) ‖w - u‖ (fun v =>
    abs_le.mp (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (w - u) v))
  intro v
  exact abs_le.mpr (hb v)

private theorem average_continuous (S : Finset V) : Continuous (average S : State V → State V) :=
  (averageLinear S).continuous_of_finiteDimensional

/-- The Lipschitz constant is independent of the strategy length. -/
theorem run_lipschitz (σ : Strategy V) : LipschitzWith 1 (run σ : State V → State V) := by
  induction σ with
  | nil => exact LipschitzWith.id
  | cons S σ ih =>
    change LipschitzWith 1 (fun w => run σ (average S w))
    simpa only [one_mul, Function.comp_def] using ih.comp (average_lipschitz S)

private theorem run_continuous (σ : Strategy V) : Continuous (run σ : State V → State V) := by
  induction σ with
  | nil => exact continuous_id
  | cons S σ ih =>
    change Continuous (fun w => run σ (average S w))
    exact ih.comp (average_continuous S)

/-- The simplex of nonnegative states with prescribed total mass. -/
private def massSimplex (m : ℝ) : Set (State V) := {w | Nonnegative w ∧ mass w = m}

theorem massSimplex_isCompact (m : ℝ) : IsCompact (massSimplex (V := V) m) := by
  have hc : IsClosed {w : State V | Nonnegative w} := by
    have heq : {w : State V | Nonnegative w} = ⋂ v : V, {w : State V | (0 : ℝ) ≤ w v} := by
      ext w
      simp [Nonnegative]
    rw [heq]
    exact isClosed_iInter (fun v => isClosed_le continuous_const (continuous_apply v))
  have hm : Continuous (mass : State V → ℝ) :=
    continuous_finsetSum _ (fun v _ => continuous_apply v)
  apply (isCompact_Icc (a := (0 : State V)) (b := fun _ => m)).of_isClosed_subset
    (hc.inter (isClosed_eq hm continuous_const))
  intro w hw
  refine ⟨hw.1, fun v => ?_⟩
  have hv : w v ≤ mass w := Finset.single_le_sum (fun j _ => hw.1 j) (Finset.mem_univ v)
  exact hv.trans_eq hw.2

theorem reachable_mem_massSimplex {G : SimpleGraph V} {w u : State V}
    (hw : Nonnegative w) (hu : Reachable G w u) : u ∈ massSimplex (mass w) := by
  obtain ⟨σ, _, rfl⟩ := hu
  exact ⟨run_nonnegative σ hw, run_mass σ w⟩

private theorem energy_continuous : Continuous (energy : State V → ℝ) :=
  continuous_finsetSum _ (fun v _ => (continuous_apply v).pow 2)

/-!
## Preparation: trap a sequence near a candidate limit

Finitely many averages give a common neighborhood in which any move not fixing the candidate loses too much energy.
-/

/-- Near a candidate limit, any average that does not fix it lowers energy below its energy.
There are finitely many selected sets, so one neighborhood works for them all. -/
private theorem exists_trapping_radius (w : State V) :
    ∃ δ > 0, ∀ u : State V, dist u w < δ → ∀ S : Finset V,
      energy w ≤ energy (average S u) → average S w = w := by
  classical
  have hev : ∀ᶠ u in 𝓝 w, ∀ S : Finset V,
      energy w ≤ energy (average S u) → average S w = w := by
    apply Filter.eventually_all.mpr
    intro S
    by_cases hS : average S w = w
    · exact Filter.Eventually.of_forall (fun _ _ => hS)
    · have hlt : energy (average S w) < energy w :=
        lt_of_le_of_ne (energy_average_le S w)
          (fun he => hS ((energy_average_eq_iff S w).mp he))
      have hh : ∀ᶠ u in 𝓝 w, energy (average S u) < energy w :=
        (energy_continuous.comp (average_continuous S)).continuousAt.eventually
          (gt_mem_nhds hlt)
      exact hh.mono (fun u hu hle => (not_lt_of_ge hle hu).elim)
  exact Metric.eventually_nhds_iff.mp hev

/-- A finite strategy whose final energy is at least the candidate's energy stays trapped.
The argument also rules out a first move crossing between its level components. -/
private theorem trapped_strategy (w : State V) (δ : ℝ)
    (hδ : ∀ u : State V, dist u w < δ → ∀ S : Finset V,
      energy w ≤ energy (average S u) → average S w = w)
    (σ : Strategy V) (u : State V) (hu : dist u w < δ)
    (he : energy w ≤ energy (run σ u)) :
    (∀ S ∈ σ, average S w = w) ∧ dist (run σ u) w ≤ dist u w := by
  induction σ generalizing u with
  | nil => exact ⟨by simp, le_rfl⟩
  | cons S σ ih =>
    have hfix := hδ u hu S (he.trans (run_energy_le σ (average S u)))
    have hd : dist (average S u) w ≤ dist u w := by
      simpa only [hfix, NNReal.coe_one, one_mul] using (average_lipschitz S).dist_le_mul u w
    obtain ⟨hσ, hdist⟩ := ih (average S u) (hd.trans_lt hu) he
    refine ⟨?_, hdist.trans hd⟩
    intro T hT
    rcases List.mem_cons.mp hT with rfl | hT
    · exact hfix
    · exact hσ T hT

/-- A compactness subsequence limit is the limit of the whole sequence by energy trapping.
Retain a tail starting point after which connecting strategies use only limit-fixing moves. -/
private theorem reachable_sequence_limit (G : SimpleGraph V) (u : ℕ → State V)
    (hu : Nonnegative (u 0)) (hstep : ∀ n, Reachable G (u n) (u (n + 1))) :
    ∃ w, Nonnegative w ∧ Tendsto u atTop (𝓝 w) ∧
      ∃ N, ∀ n, N ≤ n → ∃ σ, IsLegal G σ ∧ run σ (u N) = u n ∧
        ∀ S ∈ σ, average S w = w := by
  have hreach : ∀ n m, n ≤ m → Reachable G (u n) (u m) := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => exact reachable_refl G (u n)
    | succ k _ ih => exact reachable_trans ih (hstep k)
  have hmem : ∀ n, u n ∈ massSimplex (mass (u 0)) :=
    fun n => reachable_mem_massSimplex hu (hreach 0 n (Nat.zero_le n))
  obtain ⟨w, hw, φ, hφ, hlim⟩ := (massSimplex_isCompact (mass (u 0))).tendsto_subseq hmem
  have henergy : ∀ n, energy w ≤ energy (u n) := by
    intro n
    apply le_of_tendsto (energy_continuous.continuousAt.tendsto.comp hlim)
    apply Filter.eventually_atTop.mpr
    refine ⟨n, fun k hk => ?_⟩
    obtain ⟨σ, _, hσ⟩ := hreach n (φ k) (hk.trans (hφ.id_le k))
    simpa only [Function.comp_apply, ← hσ] using run_energy_le σ (u n)
  obtain ⟨δ, hδpos, hδ⟩ := exists_trapping_radius w
  have htend : Tendsto u atTop (𝓝 w) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨k, hk⟩ := Metric.tendsto_atTop.mp hlim (min δ ε) (lt_min hδpos hε)
    have hclose := hk k le_rfl
    refine ⟨φ k, fun n hn => ?_⟩
    obtain ⟨σ, _, hσ⟩ := hreach (φ k) n hn
    have ht := trapped_strategy w δ hδ σ (u (φ k))
      ((lt_min_iff.mp hclose).1) (by simpa only [hσ] using henergy n)
    rw [hσ] at ht
    exact ht.2.trans_lt (lt_min_iff.mp hclose).2
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp htend δ hδpos
  refine ⟨w, hw.1, htend, N, fun n hn => ?_⟩
  obtain ⟨σ, hlegal, hσ⟩ := hreach N n hn
  exact ⟨σ, hlegal, hσ, (trapped_strategy w δ hδ σ (u N) (hN N le_rfl)
    (by simpa only [hσ] using henergy n)).1⟩

/-!
## Main convergence interfaces: finite attainment of the limit

Combine convergence with component-mass conservation and finite component averaging.
-/

/-- Convergence and exact finite attainment for sequences whose successive terms are
finitely reachable. Tail component masses are conserved; component averages finish
the transformation. This version is used for chains in the existence proof. -/
theorem reachable_sequence_converges (G : SimpleGraph V) (u : ℕ → State V)
    (hu : Nonnegative (u 0)) (hstep : ∀ n, Reachable G (u n) (u (n + 1))) :
    ∃ w, Nonnegative w ∧ Tendsto u atTop (𝓝 w) ∧ ∀ n, Reachable G (u n) w := by
  obtain ⟨w, hw, ht, N, hN⟩ := reachable_sequence_limit G u hu hstep
  have hs : ∀ C : (levelGraph G w).ConnectedComponent,
      ∑ v ∈ levelBlock C, u N v = ∑ v ∈ levelBlock C, w v := by
    intro C
    have hlim := tendsto_finsetSum (levelBlock C)
      (fun v _ => (tendsto_pi_nhds.mp ht) v)
    have he : (fun n => ∑ v ∈ levelBlock C, u n v) =ᶠ[atTop]
        (fun _ => ∑ v ∈ levelBlock C, u N v) := by
      apply Filter.eventually_atTop.mpr
      refine ⟨N, fun n hn => ?_⟩
      obtain ⟨σ, hlegal, hσ, hfix⟩ := hN n hn
      change (∑ v ∈ levelBlock C, u n v) = ∑ v ∈ levelBlock C, u N v
      rw [← hσ]
      exact sum_run_levelBlock σ hlegal hfix C (u N)
    exact tendsto_nhds_unique (tendsto_const_nhds.congr' he.symm) hlim
  have htail : ∀ n, N ≤ n → Reachable G (u n) w := by
    intro n hn
    apply reachable_of_levelBlock_sums G w (u n)
    intro C
    obtain ⟨σ, hlegal, hσ, hfix⟩ := hN n hn
    rw [← hσ]
    exact (sum_run_levelBlock σ hlegal hfix C (u N)).trans (hs C)
  refine ⟨w, hw, ht, fun n => ?_⟩
  by_cases hn : N ≤ n
  · exact htail n hn
  · have hnN : n ≤ N := (Nat.lt_of_not_ge hn).le
    have hreach : Reachable G (u n) (u N) := by
      clear hN hs htail hn
      induction N, hnN using Nat.le_induction with
      | base => exact reachable_refl G (u n)
      | succ k _ ih => exact reachable_trans ih (hstep k)
    exact reachable_trans hreach (htail N le_rfl)

/-- Lemma 2.2: the whole one-step sequence converges, and its limit is finitely
reachable from every term. The latter assertion is exact reachability. -/
theorem oneStep_sequence_converges (G : SimpleGraph V) (u : ℕ → State V)
    (hu : Nonnegative (u 0)) (hstep : ∀ n, OneStep G (u n) (u (n + 1))) :
    ∃ w, Nonnegative w ∧ Tendsto u atTop (𝓝 w) ∧ ∀ n, Reachable G (u n) w :=
  reachable_sequence_converges G u hu (fun n => oneStep_reachable (hstep n))

end WaterTransport
