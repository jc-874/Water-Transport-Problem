import WaterTransport2.S01_Spider

/-!
# Paper 2, Section 2: three barriers and their equality cases

Each barrier includes the last effective move at the tip and the full state
immediately after it. This equality information is needed for the length lower bound.
The root-source result assumes `1 <= m`; the leaf-source results also allow `m = 0`
so that the later arm-reduction induction reaches its base cases.

Proof route: arm geometry; tail-sum bounds and equality rigidity; root-source
barrier (Lemma 1); double-leaf barrier (Lemma 2); single-leaf barrier (Lemma 3).
The double-leaf proof uses reverse duality and the preceding single-source invariants.
-/

namespace WaterTransport.Paper2

variable {V : Type*} [Fintype V] [DecidableEq V]

/-!
## Definitions: effective-step witnesses and source states

Record the last effective target move and count genuinely state-changing operations.
-/

/-- Step `i` is effective and contains `v`; every later move containing `v` is ineffective.
The state before step `i` is obtained by executing `take i`. -/
def LastEffectiveAt (σ : Strategy V) (w : State V) (v : V)
    (i : Fin σ.length) : Prop :=
  v ∈ σ.get i ∧ Effective (σ.get i) (run (σ.take i.val) w) ∧
    ∀ j : Fin σ.length, i < j → v ∈ σ.get j →
      ¬ Effective (σ.get j) (run (σ.take j.val) w)

/-- Number of moves changing the state at their actual execution times. -/
noncomputable def effectiveCount (σ : Strategy V) (w : State V) : ℕ := by
  classical
  exact (Finset.univ.filter fun i : Fin σ.length =>
    Effective (σ.get i) (run (σ.take i.val) w)).card

/-- Unit mass on each of the two short leaves, so total mass is two. -/
noncomputable def twoLeafSource (m : ℕ) : State (Vertex m) :=
  pointMass (leafB m) + pointMass (leafC m)

/-- The double-leaf tip bound (2*m + 3)/(m + 2)^2. -/
noncomputable def doubleBarrier (m : ℕ) : ℝ := (2 * (m : ℝ) + 3) / ((m : ℝ) + 2) ^ 2

/-!
## Preparation: connected-set geometry on the long arm

Describe tails and show how a connected selected set can intersect or cross them.
-/

private def armTail (m k : ℕ) : Finset (Vertex m) :=
  Finset.univ.filter fun v => k ≤ v.val ∧ v.val ≤ m

private lemma mem_armTail (m k : ℕ) (v : Vertex m) :
    v ∈ armTail m k ↔ k ≤ v.val ∧ v.val ≤ m := by simp [armTail]

private lemma armTail_card (m k : ℕ) (hk : k ≤ m + 1) :
    (armTail m k).card = m + 1 - k := by
  have he : armTail m k = Finset.Ico (⟨k, by omega⟩ : Vertex m) ⟨m + 1, by omega⟩ := by
    ext v
    simp only [mem_armTail, Finset.mem_Ico, Fin.le_iff_val_le_val, Fin.lt_def]
    omega
  rw [he, Fin.card_Ico]

/-- A connected selected set containing two arm vertices contains every intervening arm vertex. -/
private lemma arm_between (m : ℕ) (S : Finset (Vertex m)) (hS : IsLegalMove (spider m) S)
    (u v z : Vertex m) (hu : u ∈ S) (hv : v ∈ S)
    (huarm : u.val ≤ m) (hzu : z.val ≤ u.val)
    (hvz : v.val < z.val ∨ m < v.val) : z ∈ S := by
  by_contra hz
  let H := (spider m).induce (S : Set (Vertex m))
  let P : Vertex m → Prop := fun a => z.val ≤ a.val ∧ a.val ≤ m
  have hzarm : z.val ≤ m := hzu.trans huarm
  have hcut : ∀ a b : (S : Set (Vertex m)), H.Adj a b → P a.val → P b.val := by
    intro a b hab ha
    have hza : a.val.val ≠ z.val := fun h => hz ((Fin.ext h) ▸ a.property)
    have hzb : b.val.val ≠ z.val := fun h => hz ((Fin.ext h) ▸ b.property)
    change (spider m).Adj a.val b.val at hab
    simp only [spider, SimpleGraph.fromRel_adj, root, Fin.ext_iff, Fin.val_zero] at hab
    dsimp [P] at ha ⊢
    omega
  have hwalk : ∀ a b : (S : Set (Vertex m)), H.Reachable a b → P a.val → P b.val := by
    intro a b hab
    obtain ⟨p⟩ := hab
    induction p with
    | nil => exact id
    | cons hab p ih => intro ha; exact ih (hcut _ _ hab ha)
  have hvP := hwalk ⟨u, hu⟩ ⟨v, hv⟩ (hS.2.preconnected _ _) ⟨hzu, huarm⟩
  dsimp [P] at hvP
  omega

/-- When a connected selected set crosses a tail boundary, the unselected part of the tail is still a tail. -/
private lemma tail_crossing (m k : ℕ) (S : Finset (Vertex m))
    (hS : IsLegalMove (spider m) S) (_hk : k ≤ m)
    (hint : (armTail m k ∩ S).Nonempty) (hsub : ¬ S ⊆ armTail m k) :
    (∃ l, k < l ∧ l ≤ m + 1 ∧ armTail m k \ S = armTail m l) ∧
    ((∃ l, l ≤ m + 1 ∧ armTail m k ∪ S = armTail m l) ∨
      m + 2 ≤ (armTail m k ∪ S).card ∧ armTail m 0 ⊆ armTail m k ∪ S) := by
  classical
  obtain ⟨a, ha⟩ := hint
  obtain ⟨haT, haS⟩ := Finset.mem_inter.mp ha
  obtain ⟨b, hbS, hbT⟩ := Finset.not_subset.mp hsub
  have ha := (mem_armTail m k a).mp haT
  have hb : b.val < k ∨ m < b.val := by
    rw [mem_armTail] at hbT
    omega
  let A := S.filter fun v => v.val ≤ m
  have haA : a ∈ A := Finset.mem_filter.mpr ⟨haS, ha.2⟩
  have hA : A.Nonempty := ⟨a, haA⟩
  let j := A.max' hA
  have hjA : j ∈ A := A.max'_mem hA
  have hjS := (Finset.mem_filter.mp hjA).1
  have hjm := (Finset.mem_filter.mp hjA).2
  have haj : a.val ≤ j.val := A.le_max' _ haA
  have htail : armTail m k \ S = armTail m (j.val + 1) := by
    ext z
    simp only [Finset.mem_sdiff, mem_armTail]
    constructor
    · rintro ⟨⟨hkz, hzm⟩, hzS⟩
      refine ⟨?_, hzm⟩
      by_contra hzj
      apply hzS
      exact arm_between m S hS j b z hjS hbS hjm (by omega) (by omega)
    · rintro ⟨hjz, hzm⟩
      refine ⟨⟨by omega, hzm⟩, ?_⟩
      intro hzS
      have hzj : z.val ≤ j.val := A.le_max' z (Finset.mem_filter.mpr ⟨hzS, hzm⟩)
      omega
  refine ⟨⟨j.val + 1, by omega, by omega, htail⟩, ?_⟩
  by_cases hall : ∀ v ∈ S, v.val ≤ m
  · let i := S.min' hS.1
    have hiS : i ∈ S := S.min'_mem hS.1
    have him := hall i hiS
    have hib : i.val ≤ b.val := S.min'_le _ hbS
    have hbm := hall b hbS
    have hik : i.val < k := by omega
    left
    refine ⟨i.val, by omega, ?_⟩
    ext z
    simp only [Finset.mem_union, mem_armTail]
    constructor
    · rintro (hz | hz)
      · exact ⟨by omega, hz.2⟩
      · exact ⟨S.min'_le _ hz, hall z hz⟩
    · intro hz
      by_cases hkz : k ≤ z.val
      · exact Or.inl ⟨hkz, hz.2⟩
      · right
        by_cases hzi : z = i
        · simpa [hzi] using hiS
        have hiz : i.val < z.val := by
          have hne : z.val ≠ i.val := fun h => hzi (Fin.ext h)
          omega
        exact arm_between m S hS a i z haS hiS ha.2 (by omega) (Or.inl hiz)
  · push Not at hall
    obtain ⟨v, hvS, hvm⟩ := hall
    right
    have hcover : insert v (armTail m 0) ⊆ armTail m k ∪ S := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact Finset.mem_union_right _ hvS
      have hzm := ((mem_armTail m 0 z).mp hz).2
      by_cases hkz : k ≤ z.val
      · exact Finset.mem_union_left _ ((mem_armTail m k z).mpr ⟨hkz, hzm⟩)
      · exact Finset.mem_union_right _ (arm_between m S hS a v z haS hvS ha.2
          (by omega) (Or.inr (by omega)))
    have hvout : v ∉ armTail m 0 := by rw [mem_armTail]; omega
    have hc := Finset.card_le_card hcover
    rw [Finset.card_insert_of_notMem hvout, armTail_card m 0 (by omega)] at hc
    exact ⟨by omega, fun z hz => hcover (Finset.mem_insert_of_mem hz)⟩

/-!
## Preparation: tail bounds and equality rigidity

Propagate tail-sum bounds through averaging and recover structural information whenever a bound is attained.
-/

/-- Bound the sum after a crossing average using the difference and union sums.
Equality also fixes the new mean and the sum on the difference set. -/
private lemma averaging_interpolation {V : Type*} [Fintype V] [DecidableEq V]
    (S T : Finset V) (w : State V) (C : ℝ)
    (hi : (T ∩ S).Nonempty) (hs : ¬ S ⊆ T)
    (hD : ∑ v ∈ T \ S, w v ≤ ((T \ S).card : ℝ) * C)
    (hU : ∑ v ∈ T ∪ S, w v ≤ ((T ∪ S).card : ℝ) * C) :
    (∑ v ∈ T, average S w v ≤ (T.card : ℝ) * C) ∧
    ((∑ v ∈ T, average S w v = (T.card : ℝ) * C) →
      (∑ v ∈ T \ S, w v = ((T \ S).card : ℝ) * C) ∧ mean S w = C) := by
  classical
  have hdisj : Disjoint (T \ S) S := Finset.sdiff_disjoint
  have hpart : T = (T \ S) ∪ (T ∩ S) := by ext v; simp; tauto
  have hunion : T ∪ S = (T \ S) ∪ S := by ext v; simp
  have hsum : ∑ v ∈ T, average S w v =
      (∑ v ∈ T \ S, w v) + ((T ∩ S).card : ℝ) * mean S w := by
    conv_lhs => rw [hpart, Finset.sum_union (hdisj.mono_right Finset.inter_subset_right)]
    congr 1
    · exact Finset.sum_congr rfl fun v hv => average_apply_not_mem S w (Finset.mem_sdiff.mp hv).2
    · simp only [average]
      calc
        _ = ∑ _v ∈ T ∩ S, mean S w := Finset.sum_congr rfl fun v hv => if_pos (Finset.mem_inter.mp hv).2
        _ = _ := by simp
  have hUsum : ∑ v ∈ T ∪ S, w v = (∑ v ∈ T \ S, w v) + (S.card : ℝ) * mean S w := by
    rw [hunion, Finset.sum_union hdisj, card_mul_mean]
  have hTcard : (T.card : ℝ) = (T \ S).card + (T ∩ S).card := by
    exact_mod_cast congrArg Finset.card hpart |>.trans (Finset.card_union_of_disjoint (hdisj.mono_right Finset.inter_subset_right))
  have hUcard : ((T ∪ S).card : ℝ) = (T \ S).card + S.card := by
    rw [hunion, Finset.card_union_of_disjoint hdisj, Nat.cast_add]
  have hi0 : (0 : ℝ) < (T ∩ S).card := by exact_mod_cast hi.card_pos
  have his : ((T ∩ S).card : ℝ) < S.card := by
    exact_mod_cast Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.inter_subset_right, by intro he; apply hs; rw [← he]; exact Finset.inter_subset_left⟩)
  rw [hUsum, hUcard] at hU
  rw [hsum, hTcard]
  have hbound : (∑ v ∈ T \ S, w v) + ((T ∩ S).card : ℝ) * mean S w ≤
      ((T \ S).card + (T ∩ S).card : ℝ) * C := by
    by_cases hmean : mean S w ≤ C
    · nlinarith [mul_nonneg hi0.le (sub_nonneg.mpr hmean)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr his.le) (sub_nonneg.mpr (le_of_not_ge hmean))]
  refine ⟨hbound, ?_⟩
  intro heq
  have hmean : mean S w = C := by
    apply le_antisymm
    · by_contra hn
      have hprod := mul_pos (sub_pos.mpr his) (sub_pos.mpr (lt_of_not_ge hn))
      nlinarith
    · by_contra hn
      have hprod := mul_pos hi0 (sub_pos.mpr (lt_of_not_ge hn))
      nlinarith
  exact ⟨by rw [hmean] at heq; nlinarith, hmean⟩

private lemma tail_bound_average_of_large (m : ℕ) (w : State (Vertex m)) (C : ℝ)
    (hlarge : ∀ T : Finset (Vertex m), m + 2 ≤ T.card → armTail m 0 ⊆ T →
      ∑ v ∈ T, w v ≤ (T.card : ℝ) * C)
    (hbound : ∀ k, k ≤ m + 1 → ∑ v ∈ armTail m k, w v ≤ ((armTail m k).card : ℝ) * C)
    (S : Finset (Vertex m)) (hS : IsLegalMove (spider m) S) :
    ∀ k, k ≤ m + 1 → ∑ v ∈ armTail m k, average S w v ≤ ((armTail m k).card : ℝ) * C := by
  classical
  intro k hk
  by_cases hsub : S ⊆ armTail m k
  · rw [sum_average_of_subset S _ hsub]
    exact hbound k hk
  by_cases hi : (armTail m k ∩ S).Nonempty
  · have hkm : k ≤ m := by
      obtain ⟨v, hv⟩ := hi
      have hv' := (mem_armTail m k v).mp (Finset.mem_inter.mp hv).1
      omega
    obtain ⟨⟨l, _, hl, hD⟩, hU⟩ := tail_crossing m k S hS hkm hi hsub
    apply (averaging_interpolation S (armTail m k) w C hi hsub ?_ ?_).1
    · rw [hD]; exact hbound l hl
    · rcases hU with ⟨j, hj, he⟩ | hcard
      · rw [he]; exact hbound j hj
      · exact hlarge _ hcard.1 hcard.2
  · have he : ∑ v ∈ armTail m k, average S w v = ∑ v ∈ armTail m k, w v := by
      apply Finset.sum_congr rfl
      intro v hv
      exact average_apply_not_mem S w (fun hvS => hi ⟨v, Finset.mem_inter.mpr ⟨hv, hvS⟩⟩)
    rw [he]
    exact hbound k hk

private lemma tail_bound_average (m : ℕ) (w : State (Vertex m)) (C : ℝ)
    (hw : Nonnegative w) (hC : 0 ≤ C) (hmass : mass w ≤ ((m : ℝ) + 2) * C)
    (hbound : ∀ k, k ≤ m + 1 → ∑ v ∈ armTail m k, w v ≤ ((armTail m k).card : ℝ) * C)
    (S : Finset (Vertex m)) (hS : IsLegalMove (spider m) S) :
    ∀ k, k ≤ m + 1 → ∑ v ∈ armTail m k, average S w v ≤ ((armTail m k).card : ℝ) * C := by
  apply tail_bound_average_of_large m w C ?_ hbound S hS
  intro T hc _
  exact (Finset.sum_le_univ_sum_of_nonneg hw).trans (hmass.trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hC))

private lemma tail_bound_run (m : ℕ) (w : State (Vertex m)) (C : ℝ)
    (hw : Nonnegative w) (hC : 0 ≤ C) (hmass : mass w ≤ ((m : ℝ) + 2) * C)
    (hbound : ∀ k, k ≤ m + 1 → ∑ v ∈ armTail m k, w v ≤ ((armTail m k).card : ℝ) * C)
    (σ : Strategy (Vertex m)) (hσ : IsLegal (spider m) σ) :
    ∀ k, k ≤ m + 1 → ∑ v ∈ armTail m k, run σ w v ≤ ((armTail m k).card : ℝ) * C := by
  induction σ using List.reverseRecOn with
  | nil => exact hbound
  | append_singleton σ S ih =>
    obtain ⟨hσ, hS⟩ := (isLegal_append _ _ _).mp hσ
    rw [run_append]
    exact tail_bound_average m _ C (run_nonnegative σ hw) hC (by rw [run_mass]; exact hmass)
      (ih hσ) S (hS S (by simp))

private lemma tail_tip (m : ℕ) : armTail m m = {tip m} := by
  ext v
  simp only [mem_armTail, Finset.mem_singleton, Fin.ext_iff, tip]
  omega

private lemma mean_of_constant {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) (hS : S.Nonempty) (w : State V) (C : ℝ) (hc : ∀ v ∈ S, w v = C) :
    mean S w = C := by
  unfold mean
  rw [Finset.sum_congr rfl (fun v hv => hc v hv)]
  simp [hS.card_pos.ne']

private lemma tail_rigidity_average_of_large (m start : ℕ) (w : State (Vertex m)) (C : ℝ)
    (hlarge : ∀ T : Finset (Vertex m), m + 2 ≤ T.card → armTail m 0 ⊆ T →
      ∑ v ∈ T, w v ≤ (T.card : ℝ) * C)
    (hbound : ∀ k, k ≤ m + 1 → ∑ v ∈ armTail m k, w v ≤ ((armTail m k).card : ℝ) * C)
    (hrigid : ∀ k, start ≤ k → k ≤ m + 1 →
      (∑ v ∈ armTail m k, w v = ((armTail m k).card : ℝ) * C) → ∀ v ∈ armTail m k, w v = C)
    (S : Finset (Vertex m)) (hS : IsLegalMove (spider m) S) :
    ∀ k, start ≤ k → k ≤ m + 1 →
      (∑ v ∈ armTail m k, average S w v = ((armTail m k).card : ℝ) * C) →
      ∀ v ∈ armTail m k, average S w v = C := by
  classical
  intro k hstart hk heq v hv
  by_cases hsub : S ⊆ armTail m k
  · rw [sum_average_of_subset S _ hsub] at heq
    have hr := hrigid k hstart hk heq
    by_cases hvS : v ∈ S
    · rw [average_apply_mem S w hvS]
      exact mean_of_constant S hS.1 w C (fun u hu => hr u (hsub hu))
    · rw [average_apply_not_mem S w hvS]; exact hr v hv
  by_cases hi : (armTail m k ∩ S).Nonempty
  · have hkm : k ≤ m := by have hz := (mem_armTail m k v).mp hv; omega
    obtain ⟨⟨l, hkl, hl, hD⟩, hU⟩ := tail_crossing m k S hS hkm hi hsub
    have hDb : ∑ v ∈ armTail m k \ S, w v ≤ ((armTail m k \ S).card : ℝ) * C := by
      rw [hD]; exact hbound l hl
    have hUb : ∑ v ∈ armTail m k ∪ S, w v ≤ ((armTail m k ∪ S).card : ℝ) * C := by
      rcases hU with ⟨j, hj, he⟩ | hcard
      · rw [he]; exact hbound j hj
      · exact hlarge _ hcard.1 hcard.2
    obtain ⟨hDeq, hmean⟩ := (averaging_interpolation S (armTail m k) w C hi hsub hDb hUb).2 heq
    by_cases hvS : v ∈ S
    · rw [average_apply_mem S w hvS, hmean]
    · rw [average_apply_not_mem S w hvS]
      rw [hD] at hDeq
      exact hrigid l (by omega) hl hDeq v (hD ▸ Finset.mem_sdiff.mpr ⟨hv, hvS⟩)
  · have hfix : ∀ v ∈ armTail m k, average S w v = w v := by
      intro u hu
      exact average_apply_not_mem S w (fun huS => hi ⟨u, Finset.mem_inter.mpr ⟨hu, huS⟩⟩)
    rw [Finset.sum_congr rfl hfix] at heq
    rw [hfix v hv]
    exact hrigid k hstart hk heq v hv

private lemma tail_rigidity_run (m start : ℕ) (w : State (Vertex m)) (C : ℝ)
    (hw : Nonnegative w) (hC : 0 ≤ C) (hmass : mass w ≤ ((m : ℝ) + 2) * C)
    (hbound : ∀ k, k ≤ m + 1 → ∑ v ∈ armTail m k, w v ≤ ((armTail m k).card : ℝ) * C)
    (hrigid : ∀ k, start ≤ k → k ≤ m + 1 →
      (∑ v ∈ armTail m k, w v = ((armTail m k).card : ℝ) * C) → ∀ v ∈ armTail m k, w v = C)
    (σ : Strategy (Vertex m)) (hσ : IsLegal (spider m) σ) :
    ∀ k, start ≤ k → k ≤ m + 1 →
      (∑ v ∈ armTail m k, run σ w v = ((armTail m k).card : ℝ) * C) →
      ∀ v ∈ armTail m k, run σ w v = C := by
  induction σ using List.reverseRecOn with
  | nil => exact hrigid
  | append_singleton σ S ih =>
    obtain ⟨hσ, hS⟩ := (isLegal_append _ _ _).mp hσ
    rw [run_append]
    apply tail_rigidity_average_of_large m start _ C ?_
      (tail_bound_run m w C hw hC hmass hbound σ hσ) (ih hσ) S (hS S (by simp))
    intro T hc _
    exact (Finset.sum_le_univ_sum_of_nonneg (run_nonnegative σ hw)).trans
      (by change mass (run σ w) ≤ _; rw [run_mass]
          exact hmass.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hC))

/-!
## Preparation: locate the decisive move and specialize the invariants

Extract a last effective move, then establish the common invariants for root and single-leaf sources.
-/

private lemma exists_last_effective {V : Type*} [Fintype V] [DecidableEq V]
    (σ : Strategy V) (w : State V) (x : V) (hne : run σ w x ≠ w x) :
    ∃ i : Fin σ.length, LastEffectiveAt σ w x i ∧
      run (σ.take (i.val + 1)) w x = run σ w x := by
  classical
  induction σ using List.reverseRecOn with
  | nil => exact (hne rfl).elim
  | append_singleton σ S ih =>
    by_cases he : x ∈ S ∧ Effective S (run σ w)
    · let i : Fin (σ ++ [S]).length := ⟨σ.length, by simp⟩
      refine ⟨i, ?_, ?_⟩
      · refine ⟨?_, ?_, ?_⟩
        · simpa [i, List.get_eq_getElem, List.getElem_append] using he.1
        · simpa [i, List.get_eq_getElem, List.getElem_append] using he.2
        · intro j hij
          have hj := j.isLt
          change σ.length < j.val at hij
          simp only [List.length_append, List.length_singleton] at hj
          omega
      · have hi : i.val + 1 = (σ ++ [S]).length := by simp [i]
        rw [hi, List.take_length]
    · have hfix : run (σ ++ [S]) w x = run σ w x := by
        rw [run_append]
        change average S (run σ w) x = run σ w x
        by_cases hx : x ∈ S
        · have hh : ¬ Effective S (run σ w) := fun h => he ⟨hx, h⟩
          exact congrFun (not_not.mp hh) x
        · exact average_apply_not_mem S _ hx
      obtain ⟨i, hi, hv⟩ := ih (by rw [← hfix]; exact hne)
      let i' : Fin (σ ++ [S]).length := ⟨i.val, by simp⟩
      have hget : (σ ++ [S]).get i' = σ.get i := by
        simp [i', List.get_eq_getElem, i.isLt]
      have htake : (σ ++ [S]).take i'.val = σ.take i.val :=
        List.take_append_of_le_length i.isLt.le
      refine ⟨i', ⟨?_, ?_, ?_⟩, ?_⟩
      · rw [hget]; exact hi.1
      · rw [hget, htake]; exact hi.2.1
      · intro j hij hxj
        by_cases hj : j.val < σ.length
        · let j' : Fin σ.length := ⟨j.val, hj⟩
          have hgetj : (σ ++ [S]).get j = σ.get j' := by
            simp [j', List.get_eq_getElem, hj]
          rw [hgetj, List.take_append_of_le_length hj.le]
          exact hi.2.2 j' hij (hgetj ▸ hxj)
        · have hjval : j.val = σ.length := by have hh := j.isLt; simp at hh; omega
          have hgetj : (σ ++ [S]).get j = S := by
            simp [List.get_eq_getElem, hjval]
          rw [hgetj, hjval, List.take_append_length]
          exact fun hh => he ⟨hgetj ▸ hxj, hh⟩
      · rw [List.take_append_of_le_length (show i'.val + 1 ≤ σ.length by dsimp [i']; omega), hv, hfix]

private lemma tip_move (m : ℕ) (S : Finset (Vertex m))
    (hS : IsLegalMove (spider m) S) (htip : tip m ∈ S) :
    (∃ k, k ≤ m ∧ S = armTail m k) ∨
      (armTail m 0 ⊆ S ∧ ∃ v ∈ S, m < v.val) := by
  classical
  by_cases hleaf : ∃ v ∈ S, m < v.val
  · right
    refine ⟨?_, hleaf⟩
    obtain ⟨v, hv, hvm⟩ := hleaf
    intro z hz
    have hzm := (mem_armTail m 0 z).mp hz
    exact arm_between m S hS (tip m) v z htip hv (by rfl) hzm.2 (Or.inr hvm)
  · left
    let a := S.min' hS.1
    have haS : a ∈ S := S.min'_mem hS.1
    have hall : ∀ v ∈ S, v.val ≤ m := by intro v hv; by_contra hn; exact hleaf ⟨v, hv, by omega⟩
    refine ⟨a.val, hall a haS, ?_⟩
    ext z
    rw [mem_armTail]
    constructor
    · intro hz; exact ⟨S.min'_le _ hz, hall z hz⟩
    · intro hz
      by_cases hza : z = a
      · simpa [hza] using haS
      have haz : a.val < z.val := by have hn : z.val ≠ a.val := fun h => hza (Fin.ext h); omega
      exact arm_between m S hS (tip m) a z htip haS (by rfl) hz.2 (Or.inl haz)

private lemma initial_tail_zero_rigid (m start : ℕ) (x : Vertex m) (C : ℝ) (hC : 0 < C)
    (hx : ∀ k, start ≤ k → x ∉ armTail m k) :
    ∀ k, start ≤ k → k ≤ m + 1 →
      (∑ v ∈ armTail m k, pointMass x v = ((armTail m k).card : ℝ) * C) →
      ∀ v ∈ armTail m k, pointMass x v = C := by
  intro k hk _ heq v hv
  have hzero : (∑ v ∈ armTail m k, pointMass x v) = 0 := by simp [pointMass, hx k hk]
  have hcard : (0 : ℝ) < (armTail m k).card := by exact_mod_cast Finset.card_pos.mpr ⟨v, hv⟩
  have := mul_pos hcard hC
  rw [hzero] at heq
  linarith

private lemma point_tail_invariants (m start : ℕ) (x : Vertex m) (C : ℝ)
    (hC : 0 < C) (hmass : 1 ≤ ((m : ℝ) + 2) * C)
    (hinit : ∀ k, k ≤ m + 1 → x ∈ armTail m k → 1 ≤ ((armTail m k).card : ℝ) * C)
    (havoid : ∀ k, start ≤ k → x ∉ armTail m k)
    (σ : Strategy (Vertex m)) (hσ : IsLegal (spider m) σ) :
    (∀ k, k ≤ m + 1 → ∑ v ∈ armTail m k, run σ (pointMass x) v ≤ ((armTail m k).card : ℝ) * C) ∧
    (∀ k, start ≤ k → k ≤ m + 1 →
      (∑ v ∈ armTail m k, run σ (pointMass x) v = ((armTail m k).card : ℝ) * C) →
      ∀ v ∈ armTail m k, run σ (pointMass x) v = C) := by
  have hw : Nonnegative (pointMass x) := fun v => by simp [pointMass]; positivity
  have hmass' : mass (pointMass x) ≤ ((m : ℝ) + 2) * C := by simpa [mass, pointMass] using hmass
  have hbound : ∀ k, k ≤ m + 1 → ∑ v ∈ armTail m k, pointMass x v ≤ ((armTail m k).card : ℝ) * C := by
    intro k hk
    by_cases hx : x ∈ armTail m k
    · simpa [pointMass, hx] using hinit k hk hx
    · simp only [pointMass, Finset.sum_ite_eq', hx, if_false]; positivity
  exact ⟨tail_bound_run m _ C hw hC.le hmass' hbound σ hσ,
    tail_rigidity_run m start _ C hw hC.le hmass' hbound
      (initial_tail_zero_rigid m start x C hC havoid) σ hσ⟩

private lemma root_invariants (m : ℕ) (σ : Strategy (Vertex m)) (hσ : IsLegal (spider m) σ) :
    (∀ k, k ≤ m + 1 → ∑ v ∈ armTail m k, run σ (pointMass (root m)) v ≤
      ((armTail m k).card : ℝ) * (1 / ((m : ℝ) + 1))) ∧
    (∀ k, 1 ≤ k → k ≤ m + 1 →
      (∑ v ∈ armTail m k, run σ (pointMass (root m)) v = ((armTail m k).card : ℝ) * (1 / ((m : ℝ) + 1))) →
      ∀ v ∈ armTail m k, run σ (pointMass (root m)) v = 1 / ((m : ℝ) + 1)) := by
  have hC : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  apply point_tail_invariants m 1 (root m) _ (by positivity) ?_ ?_ ?_ σ hσ
  · rw [mul_one_div, le_div_iff₀ hC]; linarith
  · intro k hk hx
    have hk0 : k = 0 := by have h := (mem_armTail m k _).mp hx; simp [root] at h; omega
    subst k
    simp [armTail_card, Nat.cast_add, hC.ne']
  · intro k hk
    rw [mem_armTail]
    simp only [root, Fin.val_zero]
    omega

private lemma leaf_source_invariants (m : ℕ) (x : Vertex m) (hx : m < x.val)
    (σ : Strategy (Vertex m)) (hσ : IsLegal (spider m) σ) :
    (∀ k, k ≤ m + 1 → ∑ v ∈ armTail m k, run σ (pointMass x) v ≤
      ((armTail m k).card : ℝ) * (1 / ((m : ℝ) + 2))) ∧
    (∀ k, 0 ≤ k → k ≤ m + 1 →
      (∑ v ∈ armTail m k, run σ (pointMass x) v = ((armTail m k).card : ℝ) * (1 / ((m : ℝ) + 2))) →
      ∀ v ∈ armTail m k, run σ (pointMass x) v = 1 / ((m : ℝ) + 2)) := by
  have hC : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  apply point_tail_invariants m 0 x _ (by positivity) ?_ ?_ ?_ σ hσ
  · simp [hC.ne']
  · intro k hk hx
    have h := (mem_armTail m k _).mp hx
    omega
  · intro k hk
    rw [mem_armTail]
    omega



private lemma ineffective_of_constant {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) (hS : S.Nonempty) (w : State V) (C : ℝ) (hc : ∀ v ∈ S, w v = C) :
    ¬ Effective S w := by
  apply not_not.mpr
  funext v
  by_cases hv : v ∈ S
  · rw [average_apply_mem S w hv, mean_of_constant S hS w C hc, hc v hv]
  · exact average_apply_not_mem S w hv

private lemma average_full_mass {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) (w : State V) (hw : Nonnegative w) (C : ℝ)
    (hmean : mean S w = C) (hfull : ∑ v ∈ S, w v = mass w) :
    average S w = profileBlock S C := by
  funext v
  by_cases hv : v ∈ S
  · simp [average, profileBlock, hv, hmean]
  · have hle : w v + ∑ u ∈ S, w u ≤ mass w := by
      rw [← Finset.sum_insert hv]
      exact Finset.sum_le_univ_sum_of_nonneg hw
    have hz : w v = 0 := by rw [hfull] at hle; linarith [hw v]
    simp [average, profileBlock, hv, hz]

private lemma armTail_zero (m : ℕ) : armTail m 0 = pathPrefix m m := by
  ext v
  simp [armTail, pathPrefix]


private lemma run_positive_at {V : Type*} [Fintype V] [DecidableEq V]
    (σ : Strategy V) (w : State V) (hw : Nonnegative w) (x : V) (hx : 0 < w x) :
    0 < run σ w x := by
  induction σ generalizing w with
  | nil => exact hx
  | cons S σ ih =>
    apply ih _ (average_nonnegative S hw)
    by_cases hxS : x ∈ S
    · rw [average_apply_mem S w hxS]
      apply div_pos
      · exact hx.trans_le (Finset.single_le_sum (fun v _ => hw v) hxS)
      · exact_mod_cast Finset.card_pos.mpr ⟨x, hxS⟩
    · rw [average_apply_not_mem S w hxS]; exact hx

/-!
## Lemma 1: root-source barrier and equality

Bound the tip by 1/(m+1) and identify the entire state at the decisive move when equality holds.
-/

/-- Lemma 1, inequality: the root-source tip bound, including the reduced-arm case `m = 1`. -/
theorem root_barrier (m : ℕ) (hm : 1 ≤ m) (σ : Strategy (Vertex m))
    (hσ : IsLegal (spider m) σ) :
    run σ (pointMass (root m)) (tip m) ≤ 1 / ((m : ℝ) + 1) := by
  clear hm -- The inequality also holds for m = 0; this public interface retains its stated domain.
  simpa [tail_tip] using (root_invariants m σ hσ).1 m (by omega)

/-- Lemma 1, equality: the last effective tip move is the whole long arm;
immediately afterwards that arm is uniform and both short leaves are still zero. -/
theorem root_barrier_eq (m : ℕ) (hm : 1 ≤ m) (σ : Strategy (Vertex m))
    (hσ : IsLegal (spider m) σ)
    (heq : run σ (pointMass (root m)) (tip m) = 1 / ((m : ℝ) + 1)) :
    ∃ i : Fin σ.length, LastEffectiveAt σ (pointMass (root m)) (tip m) i ∧
      σ.get i = pathPrefix m m ∧
      run (σ.take (i.val + 1)) (pointMass (root m)) =
        profileBlock (pathPrefix m m) (1 / ((m : ℝ) + 1)) := by
  classical
  have hC : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hne : run σ (pointMass (root m)) (tip m) ≠ pointMass (root m) (tip m) := by
    rw [heq]
    have ht : tip m ≠ root m := by
      intro ht
      have hv := congrArg Fin.val ht
      change m = 0 at hv
      omega
    simp only [pointMass, if_neg ht]
    positivity
  obtain ⟨i, hi, hvalue⟩ := exists_last_effective σ (pointMass (root m)) (tip m) hne
  let w := run (σ.take i.val) (pointMass (root m))
  let S := σ.get i
  have hS : IsLegalMove (spider m) S := hσ S (List.get_mem _ _)
  have hτ : IsLegal (spider m) (σ.take i.val) := fun T hT => hσ T (List.mem_of_mem_take hT)
  have hw : Nonnegative w := run_nonnegative _ (fun v => by simp [pointMass]; positivity)
  have hmass : mass w = 1 := by dsimp [w]; rw [run_mass]; simp [mass, pointMass]
  have hstep : run (σ.take (i.val + 1)) (pointMass (root m)) = average S w := by
    rw [List.take_succ_eq_append_getElem i.isLt, run_append]; rfl
  have hmean : mean S w = 1 / ((m : ℝ) + 1) := by
    rw [hstep, average_apply_mem S w hi.1] at hvalue
    exact hvalue.trans heq
  have hpath : S = armTail m 0 := by
    rcases tip_move m S hS hi.1 with ⟨k, hk, hSk⟩ | ⟨hcover, v, hv, hvm⟩
    · by_cases hk0 : k = 0
      · simpa [hk0] using hSk
      have hsum : ∑ v ∈ armTail m k, w v = ((armTail m k).card : ℝ) * (1 / ((m : ℝ) + 1)) := by
        rw [← hSk, ← card_mul_mean, hmean]
      have hc := (root_invariants m _ hτ).2 k (by omega) (by omega) hsum
      exact (hi.2.1 (not_not.mp (ineffective_of_constant S hS.1 w _ (by simpa [hSk] using hc)))).elim
    · have hvout : v ∉ armTail m 0 := by rw [mem_armTail]; omega
      have hcard : m + 2 ≤ S.card := by
        have h := Finset.card_le_card (Finset.insert_subset_iff.mpr ⟨hv, hcover⟩)
        rw [Finset.card_insert_of_notMem hvout, armTail_card m 0 (by omega)] at h
        omega
      have hsum : (S.card : ℝ) * (1 / ((m : ℝ) + 1)) ≤ 1 := by
        rw [← hmean, card_mul_mean, ← hmass]
        exact Finset.sum_le_univ_sum_of_nonneg hw
      rw [mul_one_div, div_le_iff₀ hC] at hsum
      have hc : (m : ℝ) + 2 ≤ S.card := by exact_mod_cast hcard
      linarith
  refine ⟨i, hi, hpath.trans (armTail_zero m), ?_⟩
  rw [hstep]
  have hfull : ∑ v ∈ S, w v = mass w := by
    rw [← card_mul_mean, hmean, hpath, armTail_card m 0 (by omega), hmass]
    simp [Nat.cast_add, hC.ne']
  have := average_full_mass S w hw _ hmean hfull
  simpa [hpath, armTail_zero] using this

/-!
## Preparation for Lemma 2: the double-leaf source

Use single-leaf duality to control the short leaves, then establish the tail invariant and effective-step count.
-/

private lemma total_arm (m : ℕ) (w : State (Vertex m)) :
    mass w = (∑ v ∈ armTail m 0, w v) + w (leafB m) + w (leafC m) := by
  have hB : leafB m ∉ armTail m 0 := by rw [mem_armTail]; simp only [leafB]; omega
  have hC : leafC m ∉ insert (leafB m) (armTail m 0) := by
    simp only [Finset.mem_insert, mem_armTail, leafB, leafC, Fin.ext_iff]
    omega
  have hV : (Finset.univ : Finset (Vertex m)) = insert (leafC m) (insert (leafB m) (armTail m 0)) := by
    ext v
    simp only [Finset.mem_univ, Finset.mem_insert, mem_armTail, leafB, leafC, Fin.ext_iff, true_iff]
    have hv := v.isLt
    omega
  unfold mass
  rw [hV, Finset.sum_insert hC, Finset.sum_insert hB]
  ring

/-- Reverse-strategy duality converts a single-leaf tail bound into a lower bound
on the short-leaf levels for the double-leaf source. -/
private lemma double_leaf_lower (m : ℕ) (σ : Strategy (Vertex m))
    (hσ : IsLegal (spider m) σ) (x : Vertex m) (hx : m < x.val) :
    1 / ((m : ℝ) + 2) ≤ run σ (twoLeafSource m) x := by
  have hrev : IsLegal (spider m) σ.reverse := fun S hS => hσ S (List.mem_reverse.mp hS)
  have hb := (leaf_source_invariants m x hx σ.reverse hrev).1 0 (by omega)
  rw [armTail_card m 0 (by omega)] at hb
  have hmass := reverseProfile_mass σ x
  rw [total_arm] at hmass
  rw [reverseProfile_duality]
  have hp : pairing (reverseProfile σ x) (twoLeafSource m) =
      reverseProfile σ x (leafB m) + reverseProfile σ x (leafC m) := by
    simp [pairing, twoLeafSource, pointMass, mul_add, Finset.sum_add_distrib, mul_ite]
  rw [hp]
  change (∑ v ∈ armTail m 0, reverseProfile σ x v) ≤ _ at hb
  have hn : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  have hid : ((m + 1 : ℕ) : ℝ) * (1 / ((m : ℝ) + 2)) + 1 / ((m : ℝ) + 2) = 1 := by
    push_cast; field_simp; ring
  simp only [Nat.sub_zero] at hb
  linarith

private lemma double_large_bound (m : ℕ) (w : State (Vertex m))
    (hw : Nonnegative w) (hmass : mass w = 2)
    (hlow : ∀ x : Vertex m, m < x.val → 1 / ((m : ℝ) + 2) ≤ w x)
    (T : Finset (Vertex m)) (hc : m + 2 ≤ T.card) (hcover : armTail m 0 ⊆ T) :
    ∑ v ∈ T, w v ≤ (T.card : ℝ) * doubleBarrier m := by
  classical
  have hn : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  by_cases hT : T = Finset.univ
  · rw [hT]
    change mass w ≤ _
    rw [hmass, Finset.card_univ, Fintype.card_fin]
    unfold doubleBarrier
    rw [← mul_div_assoc, le_div_iff₀ (sq_pos_of_pos hn)]
    push_cast
    nlinarith [show (0 : ℝ) ≤ m by positivity]
  · obtain ⟨x, hx⟩ : ∃ x, x ∉ T := by
      by_contra hh
      push Not at hh
      exact hT (Finset.eq_univ_iff_forall.mpr hh)
    have hxm : m < x.val := by
      by_contra hh
      exact hx (hcover ((mem_armTail m 0 x).mpr ⟨by omega, by omega⟩))
    have hcard : T.card = m + 2 := by
      have hlt := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hT)
      rw [Finset.card_univ, Fintype.card_fin] at hlt
      omega
    have hsum : w x + ∑ v ∈ T, w v ≤ 2 := by
      rw [← Finset.sum_insert hx, ← hmass]
      exact Finset.sum_le_univ_sum_of_nonneg hw
    have hid : ((m + 2 : ℕ) : ℝ) * doubleBarrier m = 2 - 1 / ((m : ℝ) + 2) := by
      unfold doubleBarrier
      push_cast
      field_simp
      ring
    rw [hcard, hid]
    linarith [hlow x hxm]

private lemma double_invariants (m : ℕ) (σ : Strategy (Vertex m)) (hσ : IsLegal (spider m) σ) :
    (∀ k, k ≤ m + 1 → ∑ v ∈ armTail m k, run σ (twoLeafSource m) v ≤
      ((armTail m k).card : ℝ) * doubleBarrier m) ∧
    (∀ k, 0 ≤ k → k ≤ m + 1 →
      (∑ v ∈ armTail m k, run σ (twoLeafSource m) v = ((armTail m k).card : ℝ) * doubleBarrier m) →
      ∀ v ∈ armTail m k, run σ (twoLeafSource m) v = doubleBarrier m) := by
  have hC : 0 < doubleBarrier m := by unfold doubleBarrier; positivity
  have hw : Nonnegative (twoLeafSource m) := fun v => by
    simp only [twoLeafSource, Pi.add_apply, pointMass]; split_ifs <;> norm_num
  induction σ using List.reverseRecOn with
  | nil =>
    have hzero : ∀ k, ∑ v ∈ armTail m k, twoLeafSource m v = 0 := by
      intro k
      apply Finset.sum_eq_zero
      intro v hv
      have hv' := (mem_armTail m k v).mp hv
      have hB : v ≠ leafB m := by intro h; have := congrArg Fin.val h; simp only [leafB] at this; omega
      have hD : v ≠ leafC m := by intro h; have := congrArg Fin.val h; simp only [leafC] at this; omega
      simp [twoLeafSource, pointMass, hB, hD]
    constructor
    · intro k hk
      simp only [run_nil, hzero]
      positivity
    · intro k hk hkm heq v hv
      rw [run_nil, hzero] at heq
      have hcard : (0 : ℝ) < (armTail m k).card := by exact_mod_cast Finset.card_pos.mpr ⟨v, hv⟩
      have := mul_pos hcard hC
      linarith
  | append_singleton σ S ih =>
    obtain ⟨hσ, hS⟩ := (isLegal_append _ _ _).mp hσ
    have hlarge := double_large_bound m (run σ (twoLeafSource m)) (run_nonnegative σ hw)
      (by rw [run_mass]; norm_num [mass, twoLeafSource, pointMass, Finset.sum_add_distrib])
      (double_leaf_lower m σ hσ)
    rw [run_append]
    exact ⟨tail_bound_average_of_large m _ _ hlarge (ih hσ).1 S (hS S (by simp)),
      tail_rigidity_average_of_large m 0 _ _ hlarge (ih hσ).1 (ih hσ).2 S (hS S (by simp))⟩

/-!
## Lemma 2: double-leaf barrier and equality

Prove the numerical bound, then derive the two possible equality states and the requirement of two effective moves.
-/

/-- Lemma 2, inequality: every legal strategy from the double-leaf source satisfies the tip bound. -/
theorem double_leaf_barrier (m : ℕ) (σ : Strategy (Vertex m))
    (hσ : IsLegal (spider m) σ) :
    run σ (twoLeafSource m) (tip m) ≤ doubleBarrier m := by
  simpa [tail_tip] using (double_invariants m σ hσ).1 m (by omega)

private lemma large_arm_shape (m : ℕ) (S : Finset (Vertex m))
    (hcover : armTail m 0 ⊆ S) (hc : m + 2 ≤ S.card) (hn : S ≠ Finset.univ) :
    ∃ b c : Vertex m, ((b = leafB m ∧ c = leafC m) ∨ (b = leafC m ∧ c = leafB m)) ∧
      S = insert b (armTail m 0) ∧ c ∉ S ∧ Finset.univ = insert c S := by
  classical
  obtain ⟨c, hcS⟩ : ∃ c, c ∉ S := by
    by_contra hh; push Not at hh; exact hn (Finset.eq_univ_iff_forall.mpr hh)
  have hcm : m < c.val := by
    by_contra hh; exact hcS (hcover ((mem_armTail m 0 c).mpr ⟨by omega, by omega⟩))
  have hcard : S.card = m + 2 := by
    have hh := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hn)
    rw [Finset.card_univ, Fintype.card_fin] at hh
    omega
  have hV : Finset.univ = insert c S := by
    apply (Finset.eq_univ_of_card _ ?_).symm
    rw [Finset.card_insert_of_notMem hcS, hcard, Fintype.card_fin]
  have hchoice : c = leafB m ∨ c = leafC m := by
    have hcfin := c.isLt
    simp only [leafB, leafC, Fin.ext_iff]
    omega
  have finish (b : Vertex m) (hbm : m < b.val) (hbc : b ≠ c) : S = insert b (armTail m 0) := by
    have hbS : b ∈ S := by
      have hb : b ∈ insert c S := hV ▸ Finset.mem_univ b
      exact (Finset.mem_insert.mp hb).resolve_left hbc
    have hbout : b ∉ armTail m 0 := by rw [mem_armTail]; omega
    apply (Finset.eq_of_subset_of_card_le (Finset.insert_subset_iff.mpr ⟨hbS, hcover⟩) ?_).symm
    rw [Finset.card_insert_of_notMem hbout, armTail_card m 0 (by omega), hcard]
    omega
  rcases hchoice with rfl | rfl
  · refine ⟨leafC m, leafB m, Or.inr ⟨rfl, rfl⟩, finish _ (by simp [leafC]) ?_, hcS, hV⟩
    intro hh; have hh' := congrArg Fin.val hh; change m + 2 = m + 1 at hh'; omega
  · refine ⟨leafB m, leafC m, Or.inl ⟨rfl, rfl⟩, finish _ (by simp [leafB]) ?_, hcS, hV⟩
    intro hh; have hh' := congrArg Fin.val hh; change m + 1 = m + 2 at hh'; omega

private lemma two_effective_steps {V : Type*} [Fintype V] [DecidableEq V]
    (σ : Strategy V) (w : State V) (i : Fin σ.length)
    (hi : Effective (σ.get i) (run (σ.take i.val) w))
    (x : V) (hx : run (σ.take i.val) w x ≠ w x) : 2 ≤ effectiveCount σ w := by
  classical
  obtain ⟨j, hj, _⟩ := exists_last_effective (σ.take i.val) w x hx
  have hji : j.val < i.val := j.isLt.trans_le (List.length_take_le _ _)
  let j' : Fin σ.length := ⟨j.val, hji.trans i.isLt⟩
  have hget : (σ.take i.val).get j = σ.get j' := by simp [List.get_eq_getElem, j']
  have htake : (σ.take i.val).take j.val = σ.take j.val := by rw [List.take_take, Nat.min_eq_left hji.le]
  have hj' : Effective (σ.get j') (run (σ.take j'.val) w) := by
    have hh := hj.2.1
    rw [hget, htake] at hh
    exact hh
  change 1 < (Finset.univ.filter fun j : Fin σ.length => Effective (σ.get j) (run (σ.take j.val) w)).card
  apply Finset.one_lt_card.mpr
  refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩,
    j', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'⟩, ?_⟩
  intro he
  have hh := congrArg Fin.val he
  change i.val = j.val at hh
  omega

/-- Lemma 2, equality: list both possible post-move states and require at least two
effective operations, rather than merely two list entries. -/
theorem double_leaf_barrier_eq (m : ℕ) (σ : Strategy (Vertex m))
    (hσ : IsLegal (spider m) σ)
    (heq : run σ (twoLeafSource m) (tip m) = doubleBarrier m) :
    2 ≤ effectiveCount σ (twoLeafSource m) ∧
    ∃ i : Fin σ.length, LastEffectiveAt σ (twoLeafSource m) (tip m) i ∧
      ∃ b c : Vertex m, ((b = leafB m ∧ c = leafC m) ∨
        (b = leafC m ∧ c = leafB m)) ∧
        σ.get i = insert b (pathPrefix m m) ∧
        run (σ.take (i.val + 1)) (twoLeafSource m) =
          profileBlock (insert b (pathPrefix m m)) (doubleBarrier m) +
          (1 / ((m : ℝ) + 2)) • pointMass c := by
  classical
  have hn : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  have hC : 0 < doubleBarrier m := by unfold doubleBarrier; positivity
  have hinit : twoLeafSource m (tip m) = 0 := by
    have hB : tip m ≠ leafB m := by intro hh; have := congrArg Fin.val hh; change m = m + 1 at this; omega
    have hD : tip m ≠ leafC m := by intro hh; have := congrArg Fin.val hh; change m = m + 2 at this; omega
    simp [twoLeafSource, pointMass, hB, hD]
  obtain ⟨i, hi, hvalue⟩ := exists_last_effective σ (twoLeafSource m) (tip m)
    (by rw [heq, hinit]; exact hC.ne')
  let w := run (σ.take i.val) (twoLeafSource m)
  let S := σ.get i
  have hS : IsLegalMove (spider m) S := hσ S (List.get_mem _ _)
  have hτ : IsLegal (spider m) (σ.take i.val) := fun T hT => hσ T (List.mem_of_mem_take hT)
  have hmass : mass w = 2 := by dsimp [w]; rw [run_mass]; norm_num [mass, twoLeafSource, pointMass, Finset.sum_add_distrib]
  have hstep : run (σ.take (i.val + 1)) (twoLeafSource m) = average S w := by
    rw [List.take_succ_eq_append_getElem i.isLt, run_append]; rfl
  have hmean : mean S w = doubleBarrier m := by
    rw [hstep, average_apply_mem S w hi.1] at hvalue
    exact hvalue.trans heq
  have hcover : armTail m 0 ⊆ S ∧ m + 2 ≤ S.card := by
    rcases tip_move m S hS hi.1 with ⟨k, hk, hSk⟩ | ⟨hcover, v, hv, hvm⟩
    · have hsum : ∑ v ∈ armTail m k, w v = ((armTail m k).card : ℝ) * doubleBarrier m := by
        rw [← hSk, ← card_mul_mean, hmean]
      have hc := (double_invariants m _ hτ).2 k (by omega) (by omega) hsum
      exact (hi.2.1 (not_not.mp (ineffective_of_constant S hS.1 w _ (by simpa [hSk] using hc)))).elim
    · refine ⟨hcover, ?_⟩
      have hvout : v ∉ armTail m 0 := by rw [mem_armTail]; omega
      have hh := Finset.card_le_card (Finset.insert_subset_iff.mpr ⟨hv, hcover⟩)
      rw [Finset.card_insert_of_notMem hvout, armTail_card m 0 (by omega)] at hh
      omega
  have hnot : S ≠ Finset.univ := by
    intro hh
    have hs := card_mul_mean S w
    rw [hmean, hh] at hs
    change (Fintype.card (Vertex m) : ℝ) * doubleBarrier m = mass w at hs
    rw [Fintype.card_fin, hmass] at hs
    unfold doubleBarrier at hs
    rw [← mul_div_assoc, div_eq_iff (ne_of_gt (sq_pos_of_pos hn))] at hs
    push_cast at hs
    nlinarith [show (0 : ℝ) ≤ m by positivity]
  obtain ⟨b, c, hbc, hset, hcS, hV⟩ := large_arm_shape m S hcover.1 hcover.2 hnot
  have hbout : b ∉ armTail m 0 := by
    rcases hbc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rw [mem_armTail] <;> simp only [leafB, leafC] <;> omega
  have hcard : S.card = m + 2 := by rw [hset, Finset.card_insert_of_notMem hbout, armTail_card m 0 (by omega)]; omega
  have hcomp : mass w = w c + (S.card : ℝ) * mean S w := by
    unfold mass
    rw [hV, Finset.sum_insert hcS, card_mul_mean]
  have hid : ((m + 2 : ℕ) : ℝ) * doubleBarrier m = 2 - 1 / ((m : ℝ) + 2) := by
    unfold doubleBarrier; push_cast; field_simp; ring
  have hcval : w c = 1 / ((m : ℝ) + 2) := by rw [hmass, hmean, hcard, hid] at hcomp; linarith
  have hcinit : twoLeafSource m c = 1 := by
    have hne : leafB m ≠ leafC m := by intro hh; have := congrArg Fin.val hh; change m + 1 = m + 2 at this; omega
    rcases hbc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [twoLeafSource, pointMass, hne, hne.symm]
  have hcount : 2 ≤ effectiveCount σ (twoLeafSource m) := by
    apply two_effective_steps σ (twoLeafSource m) i hi.2.1 c
    change w c ≠ _
    rw [hcval, hcinit]
    intro hh
    have := (div_eq_iff hn.ne').mp hh
    nlinarith [show (0 : ℝ) ≤ m by positivity]
  refine ⟨hcount, i, hi, b, c, hbc, hset.trans (by rw [armTail_zero]), ?_⟩
  rw [hstep]
  funext v
  by_cases hvc : v = c
  · subst v
    have hcnot : c ∉ insert b (pathPrefix m m) := by rw [← armTail_zero, ← hset]; exact hcS
    simp [average, hcS, profileBlock, hcnot, pointMass, hcval]
  · have hvS : v ∈ S := by
      have hv : v ∈ insert c S := hV ▸ Finset.mem_univ v
      exact (Finset.mem_insert.mp hv).resolve_left hvc
    have hvset : v ∈ insert b (pathPrefix m m) := by rw [← armTail_zero, ← hset]; exact hvS
    simp [average, hvS, hmean, profileBlock, hvset, pointMass, hvc]

/-!
## Lemma 3: single-leaf barrier and equality

Give both the named-leaf result and the symmetric interface needed for the arm-reduction induction.
-/

/-- Lemma 3, inequality: from unit mass on leaf b, the tip value is at most 1/(m+2). -/
theorem single_leaf_barrier (m : ℕ) (σ : Strategy (Vertex m))
    (hσ : IsLegal (spider m) σ) :
    run σ (pointMass (leafB m)) (tip m) ≤ 1 / ((m : ℝ) + 2) := by
  simpa [tail_tip] using (leaf_source_invariants m (leafB m) (by simp [leafB]) σ hσ).1 m (by omega)

/-- Symmetric single-source bound for either short leaf, used by arm reduction. -/
theorem single_leaf_source_bound (m : ℕ) (x : Vertex m) (hx : m < x.val)
    (σ : Strategy (Vertex m)) (hσ : IsLegal (spider m) σ) :
    run σ (pointMass x) (tip m) ≤ 1 / ((m : ℝ) + 2) := by
  simpa [tail_tip] using (leaf_source_invariants m x hx σ hσ).1 m (by omega)

/-- Symmetric equality criterion with the initially nonzero short leaf supplied as a parameter. -/
theorem single_leaf_source_eq (m : ℕ) (x : Vertex m) (hx : m < x.val) (σ : Strategy (Vertex m))
    (hσ : IsLegal (spider m) σ)
    (heq : run σ (pointMass x) (tip m) = 1 / ((m : ℝ) + 2)) :
    1 ≤ effectiveCount σ (pointMass x) ∧
    ∃ i : Fin σ.length, LastEffectiveAt σ (pointMass x) (tip m) i ∧
      σ.get i = insert x (pathPrefix m m) ∧
      run (σ.take (i.val + 1)) (pointMass x) =
        profileBlock (insert x (pathPrefix m m)) (1 / ((m : ℝ) + 2)) := by
  classical
  have hC : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  have hne : run σ (pointMass x) (tip m) ≠ pointMass x (tip m) := by
    rw [heq]
    have ht : tip m ≠ x := by
      intro ht
      have hv := congrArg Fin.val ht
      change m = x.val at hv
      omega
    simp only [pointMass, if_neg ht]
    positivity
  obtain ⟨i, hi, hvalue⟩ := exists_last_effective σ (pointMass x) (tip m) hne
  have hcount : 1 ≤ effectiveCount σ (pointMass x) := by
    apply Finset.card_pos.mpr
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi.2.1⟩⟩
  let w := run (σ.take i.val) (pointMass x)
  let S := σ.get i
  have hS : IsLegalMove (spider m) S := hσ S (List.get_mem _ _)
  have hτ : IsLegal (spider m) (σ.take i.val) := fun T hT => hσ T (List.mem_of_mem_take hT)
  have hw : Nonnegative w := run_nonnegative _ (fun v => by simp [pointMass]; positivity)
  have hmass : mass w = 1 := by dsimp [w]; rw [run_mass]; simp [mass, pointMass]
  have hstep : run (σ.take (i.val + 1)) (pointMass x) = average S w := by
    rw [List.take_succ_eq_append_getElem i.isLt, run_append]; rfl
  have hmean : mean S w = 1 / ((m : ℝ) + 2) := by
    rw [hstep, average_apply_mem S w hi.1] at hvalue
    exact hvalue.trans heq
  have hcover : armTail m 0 ⊆ S ∧ ∃ v ∈ S, m < v.val := by
    rcases tip_move m S hS hi.1 with ⟨k, hk, hSk⟩ | hh
    · have hsum : ∑ v ∈ armTail m k, w v = ((armTail m k).card : ℝ) * (1 / ((m : ℝ) + 2)) := by
        rw [← hSk, ← card_mul_mean, hmean]
      have hc := (leaf_source_invariants m x hx _ hτ).2 k (by omega) (by omega) hsum
      exact (hi.2.1 (not_not.mp (ineffective_of_constant S hS.1 w _ (by simpa [hSk] using hc)))).elim
    · exact hh
  have hcard : S.card = m + 2 := by
    obtain ⟨v, hv, hvm⟩ := hcover.2
    have hvout : v ∉ armTail m 0 := by rw [mem_armTail]; omega
    have hlow := Finset.card_le_card (Finset.insert_subset_iff.mpr ⟨hv, hcover.1⟩)
    rw [Finset.card_insert_of_notMem hvout, armTail_card m 0 (by omega)] at hlow
    have hsum : (S.card : ℝ) * (1 / ((m : ℝ) + 2)) ≤ 1 := by
      rw [← hmean, card_mul_mean, ← hmass]
      exact Finset.sum_le_univ_sum_of_nonneg hw
    rw [mul_one_div, div_le_iff₀ hC] at hsum
    have hu : S.card ≤ m + 2 := by exact_mod_cast (by simpa using hsum : (S.card : ℝ) ≤ (m : ℝ) + 2)
    omega
  have hfull : ∑ v ∈ S, w v = mass w := by
    rw [← card_mul_mean, hmean, hcard, hmass]
    simp [Nat.cast_add, hC.ne']
  have hblock := average_full_mass S w hw _ hmean hfull
  have hB : x ∈ S := by
    have hpos := run_positive_at (σ.take (i.val + 1)) (pointMass x)
      (fun v => by simp [pointMass]; positivity) x (by simp [pointMass])
    rw [hstep, hblock] at hpos
    by_contra hn
    simp [profileBlock, hn] at hpos
  have hset : S = insert x (armTail m 0) := by
    apply (Finset.eq_of_subset_of_card_le (Finset.insert_subset_iff.mpr ⟨hB, hcover.1⟩) ?_).symm
    have hBnot : x ∉ armTail m 0 := by rw [mem_armTail]; omega
    rw [Finset.card_insert_of_notMem hBnot, armTail_card m 0 (by omega), hcard]
    omega
  refine ⟨hcount, i, hi, ?_, ?_⟩
  · change S = _
    rw [hset, armTail_zero]
  · rw [hstep, hblock, hset, armTail_zero]

/-- Lemma 3, equality: the last effective tip move includes the initially nonzero
short leaf and the long arm, and excludes the other short leaf. -/
theorem single_leaf_barrier_eq (m : ℕ) (σ : Strategy (Vertex m))
    (hσ : IsLegal (spider m) σ)
    (heq : run σ (pointMass (leafB m)) (tip m) = 1 / ((m : ℝ) + 2)) :
    1 ≤ effectiveCount σ (pointMass (leafB m)) ∧
    ∃ i : Fin σ.length, LastEffectiveAt σ (pointMass (leafB m)) (tip m) i ∧
      σ.get i = insert (leafB m) (pathPrefix m m) ∧
      run (σ.take (i.val + 1)) (pointMass (leafB m)) =
        profileBlock (insert (leafB m) (pathPrefix m m)) (1 / ((m : ℝ) + 2)) := by
  exact single_leaf_source_eq m (leafB m) (by simp [leafB]) σ hσ heq

end WaterTransport.Paper2
