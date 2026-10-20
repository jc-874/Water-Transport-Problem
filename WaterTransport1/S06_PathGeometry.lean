import Mathlib.Data.Fin.Rev
import WaterTransport1.S02_Strategies
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Order.Interval.Finset.Fin

/-!
# Paper 1, Section 3: path intervals and the last move

Proof route: characterize legal sets as intervals; preserve prefix-mean bounds
to solve endpoint targets; split a last interval straddling an interior target.
These arguments are independent of the two-step path theorem proved later.
-/

namespace WaterTransport

/-!
## Definitions and geometry: reflection and legal intervals

Represent the path on Fin n and identify connected selected sets with nonempty intervals.
-/

/-- Reflection as a graph automorphism of the path. -/
def pathReflection (k : ℕ) : SimpleGraph.pathGraph k ≃g SimpleGraph.pathGraph k where
  toEquiv := Fin.revPerm
  map_rel_iff' := by
    intro u v
    change (SimpleGraph.pathGraph k).Adj u.rev v.rev ↔
      (SimpleGraph.pathGraph k).Adj u v
    simp only [SimpleGraph.pathGraph_adj, Fin.val_rev]
    omega

variable {n : ℕ}

/-- The closed vertex interval `[a,b]`. It is empty when `b < a`; legality requires `a <= b`. -/
def pathInterval (a b : Fin n) : Finset (Fin n) := Finset.Icc a b

theorem pathInterval_legal (a b : Fin n) (hab : a ≤ b) :
    IsLegalMove (SimpleGraph.pathGraph n) (pathInterval a b) := by
  suffices aux : ∀ k, ∀ a b : Fin n, b.val < k → a ≤ b →
      IsLegalMove (SimpleGraph.pathGraph n) (pathInterval a b) from aux n a b b.isLt hab
  intro k
  induction k with
  | zero => intro a b hb; omega
  | succ k ih =>
    intro a b hb hab
    by_cases he : a = b
    · subst b
      refine ⟨⟨a, by simp [pathInterval]⟩, ?_⟩
      have hs : (pathInterval a a : Set (Fin n)) = {a} := by ext v; simp [pathInterval]
      rw [hs]
      exact SimpleGraph.Connected.of_subsingleton
    · have hpos : 0 < b.val := by
        have hne : a.val ≠ b.val := fun h => he (Fin.ext h)
        omega
      let p : Fin n := ⟨b.val - 1, by omega⟩
      have hap : a ≤ p := by
        have hne : a.val ≠ b.val := fun h => he (Fin.ext h)
        change a.val ≤ b.val - 1
        omega
      have hp := ih a p (by dsimp [p]; omega) hap
      have hAdj : (SimpleGraph.pathGraph n).Adj p b := by
        apply SimpleGraph.pathGraph_adj.mpr
        left
        dsimp [p]
        omega
      have hpair := SimpleGraph.induce_pair_connected_of_adj hAdj
      have hs : (pathInterval a b : Set (Fin n)) =
          (pathInterval a p : Set (Fin n)) ∪ {p, b} := by
        ext v
        simp only [Finset.mem_coe, pathInterval, Finset.mem_Icc,
          Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
        simp only [Fin.le_iff_val_le_val, Fin.ext_iff]
        dsimp [p]
        omega
      refine ⟨⟨a, Finset.mem_Icc.mpr ⟨le_rfl, hab⟩⟩, ?_⟩
      rw [hs]
      exact SimpleGraph.induce_union_connected hp.2.preconnected hpair.preconnected
        ⟨p, Finset.mem_Icc.mpr ⟨hap, le_rfl⟩, by simp⟩

/-- Legal sets are precisely nonempty intervals, using connectivity inside the induced subgraph. -/
theorem path_legal_iff_interval (S : Finset (Fin n)) :
    IsLegalMove (SimpleGraph.pathGraph n) S ↔
      ∃ a b : Fin n, a ≤ b ∧ S = pathInterval a b := by
  constructor
  · intro hS
    let a := S.min' hS.1
    let b := S.max' hS.1
    have ha : a ∈ S := S.min'_mem hS.1
    have hb : b ∈ S := S.max'_mem hS.1
    refine ⟨a, b, S.min'_le b hb, ?_⟩
    ext z
    constructor
    · intro hz
      exact Finset.mem_Icc.mpr ⟨S.min'_le z hz, S.le_max' z hz⟩
    · intro hz
      have hzI := Finset.mem_Icc.mp hz
      by_contra hnot
      let H := (SimpleGraph.pathGraph n).induce (S : Set (Fin n))
      have hne : ∀ u : (S : Set (Fin n)), u.val ≠ z := fun u he => hnot (he ▸ u.property)
      -- A missing vertex z separates the left and right parts: no path edge can cross it.
      have hcut : ∀ u v : (S : Set (Fin n)), H.Adj u v → u.val < z → v.val < z := by
        intro u v hadj hlt
        have hadj' : u.val.val + 1 = v.val.val ∨ v.val.val + 1 = u.val.val :=
          SimpleGraph.pathGraph_adj.mp hadj
        have hnv : v.val.val ≠ z.val := fun h => hne v (Fin.ext h)
        omega
      have hwalk : ∀ u v : (S : Set (Fin n)), H.Reachable u v → u.val < z → v.val < z := by
        intro u v hp
        obtain ⟨p⟩ := hp
        induction p with
        | nil => exact id
        | cons hadj p ih => intro hu; exact ih (hcut _ _ hadj hu)
      have haz : a < z := lt_of_le_of_ne hzI.1 (hne ⟨a, ha⟩)
      have hbz := hwalk ⟨a, ha⟩ ⟨b, hb⟩ (hS.2.preconnected ⟨a, ha⟩ ⟨b, hb⟩) haz
      exact not_lt_of_ge hzI.2 hbz
  · rintro ⟨a, b, hab, rfl⟩
    exact pathInterval_legal a b hab

/-!
## Endpoint preparation: prefix-mean invariants

Control every prefix sum through arbitrary interval averages.
-/

/-- Split a prefix sum into the prefix to the left of an interval and the interval sum. -/
private theorem prefix_sum_split (w : State (Fin n)) (a b : Fin n) (hab : a ≤ b) :
    ∑ v ∈ Finset.Iic b, w v =
      (∑ v ∈ Finset.Iio a, w v) + ∑ v ∈ Finset.Icc a b, w v := by
  have heq : Finset.Iic b = Finset.Iio a ∪ Finset.Icc a b := by
    ext v
    simp only [Finset.mem_Iic, Finset.mem_union, Finset.mem_Iio, Finset.mem_Icc]
    constructor
    · intro hv
      by_cases h : v < a
      · exact Or.inl h
      · exact Or.inr ⟨le_of_not_gt h, hv⟩
    · rintro (h | h)
      · exact h.le.trans hab
      · exact h.2
  rw [heq, Finset.sum_union]
  exact Finset.disjoint_left.mpr (fun v hv hv' =>
    (not_lt_of_ge (Finset.mem_Icc.mp hv').1) (Finset.mem_Iio.mp hv))

private theorem prefix_bound_Iio (w : State (Fin n)) (M : ℝ)
    (h : ∀ b, ∑ v ∈ Finset.Iic b, w v ≤ (Finset.Iic b).card * M) (a : Fin n) :
    ∑ v ∈ Finset.Iio a, w v ≤ (Finset.Iio a).card * M := by
  by_cases ha : a.val = 0
  · have he : Finset.Iio a = ∅ := by
      ext v
      simp only [Finset.mem_Iio, Finset.notMem_empty, iff_false]
      change ¬ v.val < a.val
      omega
    simp [he]
  · let p : Fin n := ⟨a.val - 1, by omega⟩
    have he : Finset.Iio a = Finset.Iic p := by
      ext v
      simp only [Finset.mem_Iio, Finset.mem_Iic]
      change v.val < a.val ↔ v.val ≤ a.val - 1
      omega
    rw [he]
    exact h p

/-- Interval averaging preserves an upper bound on every prefix mean.
Across the averaged interval, new prefix sums interpolate between its two old endpoint sums. -/
private theorem prefix_bound_average (w : State (Fin n)) (M : ℝ)
    (h : ∀ b, ∑ v ∈ Finset.Iic b, w v ≤ (Finset.Iic b).card * M)
    (a b : Fin n) (hab : a ≤ b) :
    ∀ c, ∑ v ∈ Finset.Iic c, average (pathInterval a b) w v ≤ (Finset.Iic c).card * M := by
  intro c
  by_cases hca : c < a
  · have he : ∑ v ∈ Finset.Iic c, average (pathInterval a b) w v =
        ∑ v ∈ Finset.Iic c, w v := by
      apply Finset.sum_congr rfl
      intro v hv
      apply average_apply_not_mem
      intro hmem
      exact (not_lt_of_ge (Finset.mem_Icc.mp hmem).1)
        ((Finset.mem_Iic.mp hv).trans_lt hca)
    rw [he]
    exact h c
  by_cases hbc : b ≤ c
  · rw [sum_average_of_subset (pathInterval a b) (Finset.Iic c) (fun v hv =>
      Finset.mem_Iic.mpr ((Finset.mem_Icc.mp hv).2.trans hbc)) w]
    exact h c
  have hac : a ≤ c := le_of_not_gt hca
  have hcb : c ≤ b := (lt_of_not_ge hbc).le
  have hleft : ∑ v ∈ Finset.Iio a, average (pathInterval a b) w v =
      ∑ v ∈ Finset.Iio a, w v := by
    apply Finset.sum_congr rfl
    intro v hv
    apply average_apply_not_mem
    exact fun hmem => (not_lt_of_ge (Finset.mem_Icc.mp hmem).1) (Finset.mem_Iio.mp hv)
  have hmid : ∑ v ∈ Finset.Icc a c, average (pathInterval a b) w v =
      (Finset.Icc a c).card * mean (pathInterval a b) w := by
    calc
      _ = ∑ _v ∈ Finset.Icc a c, mean (pathInterval a b) w := by
        apply Finset.sum_congr rfl
        intro v hv
        exact average_apply_mem _ _
          (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hv).1, (Finset.mem_Icc.mp hv).2.trans hcb⟩)
      _ = _ := by simp
  have hA := prefix_bound_Iio w M h a
  have hB := h b
  rw [prefix_sum_split w a b hab, ← card_mul_mean (Finset.Icc a b) w] at hB
  change (∑ v ∈ Finset.Iio a, w v) + (pathInterval a b).card * mean (pathInterval a b) w ≤
    (Finset.Iic b).card * M at hB
  have hcardB : ((Finset.Iic b).card : ℝ) =
      (Finset.Iio a).card + (pathInterval a b).card := by
    simp only [Fin.card_Iic, Fin.card_Iio, pathInterval, Fin.card_Icc]
    norm_cast
    have : a.val ≤ b.val := hab
    omega
  have hcardC : ((Finset.Iic c).card : ℝ) =
      (Finset.Iio a).card + (Finset.Icc a c).card := by
    simp only [Fin.card_Iic, Fin.card_Iio, Fin.card_Icc]
    norm_cast
    have : a.val ≤ c.val := hac
    omega
  have hcard : ((Finset.Icc a c).card : ℝ) ≤ (pathInterval a b).card := by
    exact_mod_cast Finset.card_le_card (show Finset.Icc a c ⊆ pathInterval a b from
      fun v hv => Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hv).1, (Finset.mem_Icc.mp hv).2.trans hcb⟩)
  rw [prefix_sum_split _ a c hac, hleft, hmid, hcardC]
  rw [hcardB] at hB
  by_cases hm : mean (pathInterval a b) w ≤ M
  · nlinarith [mul_nonneg (Nat.cast_nonneg (Finset.Icc a c).card) (sub_nonneg.mpr hm)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hcard) (sub_nonneg.mpr (le_of_not_ge hm))]

/-!
## Endpoint conclusion: one initial prefix dominates all strategies

Choose a maximal initial prefix mean and propagate its bound to the target endpoint.
-/

/-- An initial prefix mean dominates the endpoint value of every finite legal strategy.
Singleton prefixes include the zero-step optimum; no general attainment theorem is used. -/
theorem endpoint_prefix_dominates (w : State (Fin (n + 1))) (hw : Nonnegative w) :
    ∃ b : Fin (n + 1), ∀ σ, IsLegal (SimpleGraph.pathGraph (n + 1)) σ →
      run σ w 0 ≤ mean (pathInterval 0 b) w := by
  clear hw -- The prefix comparison allows real input; this interface retains the paper's nonnegativity assumption.
  classical
  obtain ⟨b, _, hb⟩ := Finset.exists_max_image Finset.univ
    (fun b : Fin (n + 1) => mean (pathInterval 0 b) w) ⟨0, Finset.mem_univ 0⟩
  let M := mean (pathInterval 0 b) w
  have hprefix : ∀ c, ∑ v ∈ Finset.Iic c, w v ≤ (Finset.Iic c).card * M := by
    intro c
    have he : pathInterval (0 : Fin (n + 1)) c = Finset.Iic c := by
      ext v
      simp [pathInterval]
    have hm := hb c (Finset.mem_univ c)
    rw [he] at hm
    calc
      _ = (Finset.Iic c).card * mean (Finset.Iic c) w := (card_mul_mean _ w).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg _)
  have hrun : ∀ σ : Strategy (Fin (n + 1)), IsLegal (SimpleGraph.pathGraph (n + 1)) σ →
      ∀ u : State (Fin (n + 1)),
      (∀ c, ∑ v ∈ Finset.Iic c, u v ≤ (Finset.Iic c).card * M) →
      ∀ c, ∑ v ∈ Finset.Iic c, run σ u v ≤ (Finset.Iic c).card * M := by
    intro σ
    induction σ with
    | nil => intro _ u hu; exact hu
    | cons S σ ih =>
      intro hσ u hu
      obtain ⟨a, d, had, rfl⟩ := (path_legal_iff_interval S).mp ((isLegal_cons _ _ _).mp hσ).1
      exact ih ((isLegal_cons _ _ _).mp hσ).2 _ (prefix_bound_average u M hu a d had)
  refine ⟨b, fun σ hσ => ?_⟩
  have hz : Finset.Iic (0 : Fin (n + 1)) = {0} := by
    ext v
    simp only [Finset.mem_Iic, Finset.mem_singleton, Fin.le_iff_val_le_val, Fin.ext_iff]
    change v.val ≤ 0 ↔ v.val = 0
    omega
  simpa only [hz, Finset.sum_singleton, Finset.card_singleton, Nat.cast_one, one_mul] using
    hrun σ hσ w hprefix 0

/-!
## Interior-target preparation: split the final interval

A strict improvement at an interior target admits an even better split competitor.
-/

private theorem mean_average_of_singleton_inter (L R : Finset (Fin n))
    (x : Fin n) (hxL : x ∈ L) (hxR : x ∈ R) (hLR : L ∩ R = {x})
    (w : State (Fin n)) :
    (R.card : ℝ) * mean R (average L w) =
      R.card * mean R w + mean L w - w x := by
  rw [card_mul_mean, card_mul_mean]
  have he : ∑ v ∈ R.erase x, average L w v = ∑ v ∈ R.erase x, w v := by
    apply Finset.sum_congr rfl
    intro v hv
    apply average_apply_not_mem
    intro hvL
    have hx : v = x := Finset.mem_singleton.mp
      (hLR ▸ Finset.mem_inter.mpr ⟨hvL, (Finset.mem_erase.mp hv).2⟩)
    exact (Finset.mem_erase.mp hv).1 hx
  rw [← Finset.sum_erase_add R (fun v => average L w v) hxR,
    ← Finset.sum_erase_add R w hxR, he, average_apply_mem L w hxL]
  ring

/-- If averaging an interval strictly raises an interior target, splitting it at
that target and averaging the two pieces in one of the two orders is strictly better.
This comparison uses two moves in place of one. -/
private theorem path_split_improves (w : State (Fin n)) (a x b : Fin n)
    (hax : a < x) (hxb : x < b) (hraise : w x < mean (pathInterval a b) w) :
    mean (pathInterval a b) w < run [pathInterval a x, pathInterval x b] w x ∨
    mean (pathInterval a b) w < run [pathInterval x b, pathInterval a x] w x := by
  let L := pathInterval a x
  let R := pathInterval x b
  have hxL : x ∈ L := Finset.mem_Icc.mpr ⟨hax.le, le_rfl⟩
  have hxR : x ∈ R := Finset.mem_Icc.mpr ⟨le_rfl, hxb.le⟩
  have hLR : L ∩ R = {x} := by
    ext v
    simp only [L, R, pathInterval, Finset.mem_inter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · intro h; exact le_antisymm h.1.2 h.2.1
    · rintro rfl; exact ⟨⟨hax.le, le_rfl⟩, ⟨le_rfl, hxb.le⟩⟩
  have hU : L ∪ R = pathInterval a b := by
    ext v
    simp only [L, R, pathInterval, Finset.mem_union, Finset.mem_Icc]
    constructor
    · rintro (h | h)
      · exact ⟨h.1, h.2.trans hxb.le⟩
      · exact ⟨hax.le.trans h.1, h.2⟩
    · intro h
      by_cases hv : v ≤ x
      · exact Or.inl ⟨h.1, hv⟩
      · exact Or.inr ⟨(lt_of_not_ge hv).le, h.2⟩
  have hl : (1 : ℝ) < L.card := by
    have ha : a ∈ L := Finset.mem_Icc.mpr ⟨le_rfl, hax.le⟩
    exact_mod_cast Finset.one_lt_card.mpr ⟨a, ha, x, hxL, hax.ne⟩
  have hr : (1 : ℝ) < R.card := by
    have hb : b ∈ R := Finset.mem_Icc.mpr ⟨hxb.le, le_rfl⟩
    exact_mod_cast Finset.one_lt_card.mpr ⟨x, hxR, b, hb, hxb.ne⟩
  have hc : ((pathInterval a b).card : ℝ) + 1 = L.card + R.card := by
    have hh := Finset.card_union_add_card_inter L R
    rw [hU, hLR, Finset.card_singleton] at hh
    exact_mod_cast hh
  have hs : (pathInterval a b).card * mean (pathInterval a b) w + w x =
      L.card * mean L w + R.card * mean R w := by
    simpa only [hU, hLR, Finset.sum_singleton, ← card_mul_mean] using
      (Finset.sum_union_inter (s₁ := L) (s₂ := R) (f := w))
  have hc' : ((pathInterval a b).card : ℝ) = L.card + R.card - 1 := by linarith
  rw [hc'] at hs
  have h₁ := mean_average_of_singleton_inter L R x hxL hxR hLR w
  have h₂ := mean_average_of_singleton_inter R L x hxR hxL
    (by rw [Finset.inter_comm, hLR]) w
  change mean (pathInterval a b) w < average R (average L w) x ∨
    mean (pathInterval a b) w < average L (average R w) x
  rw [average_apply_mem R _ hxR, average_apply_mem L _ hxL]
  by_contra h
  obtain ⟨h₁le, h₂le⟩ := not_or.mp h
  have h₁mul := mul_le_mul_of_nonneg_left (le_of_not_gt h₁le) (Nat.cast_nonneg R.card (α := ℝ))
  have h₂mul := mul_le_mul_of_nonneg_left (le_of_not_gt h₂le) (Nat.cast_nonneg L.card (α := ℝ))
  have hA : mean (pathInterval a b) w ≤ mean L w := by
    have hh : 0 ≤ ((L.card : ℝ) - 1) * (mean L w - mean (pathInterval a b) w) := by
      nlinarith [hs, h₁mul]
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left (by linarith : (0 : ℝ) < L.card - 1)).mp hh)
  have hB : mean (pathInterval a b) w ≤ mean R w := by
    have hh : 0 ≤ ((R.card : ℝ) - 1) * (mean R w - mean (pathInterval a b) w) := by
      nlinarith [hs, h₂mul]
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left (by linarith : (0 : ℝ) < R.card - 1)).mp hh)
  have hAmul := mul_le_mul_of_nonneg_left hA (Nat.cast_nonneg L.card (α := ℝ))
  have hBmul := mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg R.card (α := ℝ))
  nlinarith

/-!
## Conclusion used by shortening: normalize the last move

Global optimality forces an endpoint last move unless that move can be removed.
-/

/-- For a globally optimal strategy, the last interval either has the target as an
endpoint or can be deleted. Global optimality permits the longer split competitor
used to rule out a strict improvement at an interior target. -/
theorem optimal_path_last_endpoint_or_prefix (w : State (Fin n)) (x a b : Fin n)
    (σ : Strategy (Fin n))
    (hopt : IsOptimal (SimpleGraph.pathGraph n) w x (σ ++ [pathInterval a b])) :
    x = a ∨ x = b ∨ IsOptimal (SimpleGraph.pathGraph n) w x σ := by
  have hσ := ((isLegal_append _ _ _).mp hopt.1).1
  by_cases hprev : run (σ ++ [pathInterval a b]) w x ≤ run σ w x
  · exact Or.inr (Or.inr ⟨hσ, fun τ hτ => (hopt.2 τ hτ).trans hprev⟩)
  have hraise := lt_of_not_ge hprev
  have hx : x ∈ pathInterval a b := by
    by_contra hnot
    rw [run_append, run_singleton, average_apply_not_mem _ _ hnot] at hraise
    exact lt_irrefl _ hraise
  have hab := Finset.mem_Icc.mp hx
  by_cases hxa : x = a
  · exact Or.inl hxa
  by_cases hxb : x = b
  · exact Or.inr (Or.inl hxb)
  have hax : a < x := lt_of_le_of_ne hab.1 (fun h => hxa h.symm)
  have hxb' : x < b := lt_of_le_of_ne hab.2 hxb
  have hval : run (σ ++ [pathInterval a b]) w x = mean (pathInterval a b) (run σ w) := by
    rw [run_append, run_singleton, average_apply_mem _ _ hx]
  rw [hval] at hraise
  have hleft : IsLegalMove (SimpleGraph.pathGraph n) (pathInterval a x) :=
    pathInterval_legal a x hax.le
  have hright : IsLegalMove (SimpleGraph.pathGraph n) (pathInterval x b) :=
    pathInterval_legal x b hxb'.le
  have hbound : ∀ τ, IsLegal (SimpleGraph.pathGraph n) τ →
      run τ (run σ w) x ≤ mean (pathInterval a b) (run σ w) := by
    intro τ hτ
    have hh := hopt.2 (σ ++ τ) ((isLegal_append _ _ _).mpr ⟨hσ, hτ⟩)
    change run (σ ++ τ) w x ≤ run (σ ++ [pathInterval a b]) w x at hh
    simpa only [run_append, hval] using hh
  have hlr : IsLegal (SimpleGraph.pathGraph n) [pathInterval a x, pathInterval x b] := by
    simp only [isLegal_cons, isLegal_nil, and_true]
    exact ⟨hleft, hright⟩
  have hrl : IsLegal (SimpleGraph.pathGraph n) [pathInterval x b, pathInterval a x] := by
    simp only [isLegal_cons, isLegal_nil, and_true]
    exact ⟨hright, hleft⟩
  rcases path_split_improves (run σ w) a x b hax hxb' hraise with h | h
  · exact (not_lt_of_ge (hbound _ hlr) h).elim
  · exact (not_lt_of_ge (hbound _ hrl) h).elim

end WaterTransport
