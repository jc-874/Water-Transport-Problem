import WaterTransport1.S06_PathGeometry
import WaterTransport1.S05_MinimalLength
import Mathlib.Data.Fin.Rev
import Mathlib.Tactic.GCongr

/-!
# Paper 1, Section 3: shortening the last three path moves

Reverse profiles reduce water-level comparisons to interpolation between two
constant blocks. Interval positions determine the candidate shorter strategies.
These algebraic comparisons hold for arbitrary real input states.

Proof route: block arithmetic; three crossing configurations; containment and
one-sided configurations; combine the cases and reflect; apply the comparison
to a globally shortest optimal strategy to prove `path_two_step_core`.
-/

namespace WaterTransport

variable {n : ℕ}

-- Shared coordinate calculation for equalities between constant interval profiles.
-- Water-level inequalities remain explicit in the individual geometric cases below.
local macro "profile_cases" "(" step:tacticSeq ")" : tactic =>
  `(tactic|
    (funext v
     ($step:tacticSeq)
     dsimp only [profileBlock, average, Pi.add_apply, Pi.zero_apply]
     simp only [Finset.mem_Icc, Finset.mem_Ico, Finset.mem_Ioc]
     split_ifs <;> first | omega | ring))

/-!
## Preparation: interval arithmetic and two-block comparisons

Compute cardinalities and means, and translate reverse-profile comparisons into forward target bounds.
-/

private theorem card_Icc_real (a b : Fin n) (hab : a ≤ b) :
    ((Finset.Icc a b).card : ℝ) = b.val + 1 - a.val := by
  rw [Fin.card_Icc, Nat.cast_sub (by have : a.val ≤ b.val := hab; omega)]
  push_cast
  ring

private theorem mean_block_right (a x b c : Fin n)
    (hab : a ≤ b) (hbx : b ≤ x) (hxc : x ≤ c) (h : ℝ) :
    mean (Finset.Icc b c) (profileBlock (Finset.Icc a x) h) =
      (x.val + 1 - b.val) * h / (c.val + 1 - b.val) := by
  have hi : Finset.Icc b c ∩ Finset.Icc a x = Finset.Icc b x := by
    ext v
    simp only [Finset.mem_inter, Finset.mem_Icc]
    constructor
    · exact fun hv => ⟨hv.1.1, hv.2.2⟩
    · exact fun hv => ⟨⟨hv.1, hv.2.trans hxc⟩, ⟨hab.trans hv.1, hv.2⟩⟩
  rw [mean_profileBlock, hi, card_Icc_real _ _ hbx,
    card_Icc_real _ _ (hbx.trans hxc)]

/-- For a nonnegative profile flat on the left and zero on the right,
moving the left cutoff rightwards cannot increase the mean. -/
private theorem mean_block_right_left_mono (a x b d c : Fin n)
    (hab : a ≤ b) (hbd : b ≤ d) (hdx : d ≤ x) (hxc : x ≤ c)
    (h : ℝ) (hh : 0 ≤ h) :
    mean (Finset.Icc d c) (profileBlock (Finset.Icc a x) h) ≤
      mean (Finset.Icc b c) (profileBlock (Finset.Icc a x) h) := by
  rw [mean_block_right a x d c (hab.trans hbd) hdx hxc,
    mean_block_right a x b c hab (hbd.trans hdx) hxc]
  have hbd' : (b.val : ℝ) ≤ d.val := by exact_mod_cast hbd
  have hdc' : (d.val : ℝ) ≤ c.val := by exact_mod_cast hdx.trans hxc
  have hxc' : (x.val : ℝ) ≤ c.val := by exact_mod_cast hxc
  apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
  nlinarith [mul_nonneg hh (mul_nonneg (sub_nonneg.mpr hbd') (sub_nonneg.mpr hxc'))]

/-- Extending a nonnegative block into its zero right tail cannot increase the mean. -/
private theorem mean_block_right_right_mono (a x b c e : Fin n)
    (hab : a ≤ b) (hbx : b ≤ x) (hxc : x ≤ c) (hce : c ≤ e)
    (h : ℝ) (hh : 0 ≤ h) :
    mean (Finset.Icc b e) (profileBlock (Finset.Icc a x) h) ≤
      mean (Finset.Icc b c) (profileBlock (Finset.Icc a x) h) := by
  rw [mean_block_right a x b e hab hbx (hxc.trans hce),
    mean_block_right a x b c hab hbx hxc]
  have hbx' : (b.val : ℝ) ≤ x.val := by exact_mod_cast hbx
  have hxc' : (x.val : ℝ) ≤ c.val := by exact_mod_cast hxc
  have hce' : (c.val : ℝ) ≤ e.val := by exact_mod_cast hce
  apply div_le_div_of_nonneg_left (mul_nonneg (by linarith) hh)
    (by linarith) (by linarith)

/-- A reverse-profile interpolation bound yields one of two forward strategies with at least the original value. -/
private theorem run_le_max_of_profile_blocks (w : State (Fin n)) (x : Fin n)
    (σ τ ρ : Strategy (Fin n)) (S T : Finset (Fin n)) (base : State (Fin n))
    (a b a₀ b₀ a₁ b₁ : ℝ)
    (hp : reverseProfile σ x = base + profileBlock S a + profileBlock T b)
    (hq : reverseProfile τ x = base + profileBlock S a₀ + profileBlock T b₀)
    (hr : reverseProfile ρ x = base + profileBlock S a₁ + profileBlock T b₁)
    (hb₀ : b₀ ≤ b) (hb₁ : b ≤ b₁) :
    run σ w x ≤ max (run τ w x) (run ρ w x) := by
  have hm₀ : mass (base + profileBlock S a + profileBlock T b) =
      mass (base + profileBlock S a₀ + profileBlock T b₀) := by
    rw [← hp, ← hq, reverseProfile_mass, reverseProfile_mass]
  have hm₁ : mass (base + profileBlock S a + profileBlock T b) =
      mass (base + profileBlock S a₁ + profileBlock T b₁) := by
    rw [← hp, ← hr, reverseProfile_mass, reverseProfile_mass]
  simpa only [reverseProfile_duality, hp, hq, hr] using
    pairing_le_max_of_two_blocks S T base w a b a₀ b₀ a₁ b₁ hm₀ hm₁ hb₀ hb₁

private theorem path_Ioc_legal (a b : Fin n) (hab : a < b) :
    IsLegalMove (SimpleGraph.pathGraph n) (Finset.Ioc a b) := by
  let d : Fin n := ⟨a.val + 1, by have := b.isLt; omega⟩
  have hd : d ≤ b := by change a.val + 1 ≤ b.val; omega
  have he : Finset.Ioc a b = pathInterval d b := by
    ext v
    simp only [Finset.mem_Ioc, pathInterval, Finset.mem_Icc,
      Fin.le_iff_val_le_val, Fin.lt_def]
    dsimp [d]
    omega
  rw [he]
  exact pathInterval_legal d b hd

private theorem mean_block_Ioc_le (a x b e c : Fin n)
    (hab : a ≤ b) (hbe : b ≤ e) (hex : e < x) (hxc : x ≤ c)
    (h : ℝ) (hh : 0 ≤ h) :
    mean (Finset.Ioc e c) (profileBlock (Finset.Icc a x) h) ≤
      mean (Finset.Icc b c) (profileBlock (Finset.Icc a x) h) := by
  let d : Fin n := ⟨e.val + 1, by have := x.isLt; omega⟩
  have hd : d ≤ x := by change e.val + 1 ≤ x.val; omega
  have he : Finset.Ioc e c = Finset.Icc d c := by
    ext v
    simp only [Finset.mem_Ioc, Finset.mem_Icc,
      Fin.le_iff_val_le_val, Fin.lt_def]
    dsimp [d]
    omega
  rw [he]
  exact mean_block_right_left_mono a x b d c hab (by change b.val ≤ e.val + 1; omega) hd hxc h hh

/-!
## Geometric cases: crossing the two profile blocks

Handle crossings within the support, beyond its right end, and beyond its left end. Each case constructs shorter competitors.
-/

/-- Crossing case 1: the third reverse average crosses the platform junction but
stays inside the left support boundary. Two shifted-junction candidates bracket it. -/
private theorem left_cross_inside_dominates (w : State (Fin n))
    (a b x c d e : Fin n) (had : a ≤ d) (hdb : d < b)
    (hbx : b ≤ x) (hxc : x < c) (hbe : b ≤ e) (hec : e < c) :
    ∃ τ, IsLegal (SimpleGraph.pathGraph n) τ ∧ τ.length ≤ 2 ∧
      run [Finset.Icc d e, Finset.Icc b c, Finset.Icc a x] w x ≤ run τ w x := by
  let C := Finset.Icc a x
  let B := Finset.Icc b c
  let A := Finset.Icc d e
  let D := Finset.Icc d c
  let T := Finset.Ioc e c
  let L := Finset.Ico a d
  let h : ℝ := 1 / C.card
  let u := profileBlock C h
  let l := mean B u
  let k := mean A (average B u)
  let q := mean D u
  have hh : 0 ≤ h := div_nonneg zero_le_one (Nat.cast_nonneg _)
  have hax : a ≤ x := had.trans (hdb.le.trans hbx)
  have hxC : x ∈ C := Finset.mem_Icc.mpr ⟨hax, le_rfl⟩
  have hD : IsLegalMove (SimpleGraph.pathGraph n) D :=
    pathInterval_legal d c (hdb.le.trans (hbx.trans hxc.le))
  have hC : IsLegalMove (SimpleGraph.pathGraph n) C := pathInterval_legal a x hax
  have hA : IsLegalMove (SimpleGraph.pathGraph n) A := pathInterval_legal d e (hdb.le.trans hbe)
  have hp : reverseProfile [A, B, C] x = profileBlock L h + profileBlock A k +
      profileBlock T l := by
    change average A (average B (average C (pointMass x))) = _
    rw [average_pointMass C x hxC]
    profile_cases (dsimp only [A, B, C, T, L, h, k, l, u])
  have hq : reverseProfile [D, C] x = profileBlock L h + profileBlock A q +
      profileBlock T q := by
    change average D (average C (pointMass x)) = _
    rw [average_pointMass C x hxC]
    profile_cases (dsimp only [C, B, A, D, T, L, h, u, l, k, q])
  have hlq : l ≤ q := mean_block_right_left_mono a x d b c had hdb.le hbx hxc.le h hh
  by_cases hex : e < x
  · let r := mean T u
    have hr : reverseProfile [T, C] x = profileBlock L h + profileBlock A h +
        profileBlock T r := by
      change average T (average C (pointMass x)) = _
      rw [average_pointMass C x hxC]
      profile_cases (dsimp only [C, B, A, D, T, L, h, u, l, k, q, r])
    have hrl : r ≤ l := mean_block_Ioc_le a x b e c (had.trans hdb.le) hbe hex hxc.le h hh
    have hval := run_le_max_of_profile_blocks w x [A, B, C] [T, C] [D, C]
      A T (profileBlock L h) k l h r q q hp hr hq hrl hlq
    rcases le_max_iff.mp hval with hv | hv
    · exact ⟨[T, C], by simp [isLegal_cons, path_Ioc_legal e c hec, hC, T], by simp, hv⟩
    · exact ⟨[D, C], by simp [isLegal_cons, hD, hC], by simp, hv⟩
  · let r := mean A u
    have hr : reverseProfile [A, C] x = profileBlock L h + profileBlock A r +
        profileBlock T 0 := by
      change average A (average C (pointMass x)) = _
      rw [average_pointMass C x hxC]
      profile_cases (dsimp only [C, B, A, D, T, L, h, u, l, k, q, r])
    have hl : 0 ≤ l := by
      apply div_nonneg _ (Nat.cast_nonneg _)
      apply Finset.sum_nonneg
      intro v _
      change 0 ≤ if v ∈ C then h else 0
      split_ifs <;> positivity
    have hval := run_le_max_of_profile_blocks w x [A, B, C] [A, C] [D, C]
      A T (profileBlock L h) k l r 0 q q hp hr hq hl hlq
    rcases le_max_iff.mp hval with hv | hv
    · exact ⟨[A, C], by simp [isLegal_cons, hA, hC], by simp, hv⟩
    · exact ⟨[D, C], by simp [isLegal_cons, hD, hC], by simp, hv⟩

private theorem path_Ico_legal (a b : Fin n) (hab : a < b) :
    IsLegalMove (SimpleGraph.pathGraph n) (Finset.Ico a b) := by
  let d : Fin n := ⟨b.val - 1, by have := b.isLt; omega⟩
  have hd : a ≤ d := by change a.val ≤ b.val - 1; omega
  have he : Finset.Ico a b = pathInterval a d := by
    ext v
    simp only [Finset.mem_Ico, pathInterval, Finset.mem_Icc,
      Fin.le_iff_val_le_val, Fin.lt_def]
    dsimp [d]
    omega
  rw [he]
  exact pathInterval_legal a d hd

/-- Crossing case 2: the third reverse average extends past the right platform.
Two candidates keep or merge the new junction at that interval's left endpoint. -/
private theorem right_cross_dominates (w : State (Fin n))
    (a b x c d e : Fin n) (hab : a ≤ b) (hbx : b ≤ x)
    (hxc : x < c) (hbd : b < d) (hdc : d ≤ c) (hce : c < e) :
    ∃ τ, IsLegal (SimpleGraph.pathGraph n) τ ∧ τ.length ≤ 2 ∧
      run [Finset.Icc d e, Finset.Icc b c, Finset.Icc a x] w x ≤ run τ w x := by
  let C := Finset.Icc a x
  let B := Finset.Icc b c
  let A := Finset.Icc d e
  let D := Finset.Icc b e
  let T := Finset.Ico b d
  let L := Finset.Ico a b
  let h : ℝ := 1 / C.card
  let u := profileBlock C h
  let l := mean B u
  let k := mean A (average B u)
  let q := mean D u
  have hh : 0 ≤ h := div_nonneg zero_le_one (Nat.cast_nonneg _)
  have hxC : x ∈ C := Finset.mem_Icc.mpr ⟨hab.trans hbx, le_rfl⟩
  have hD : IsLegalMove (SimpleGraph.pathGraph n) D :=
    pathInterval_legal b e (hbx.trans (hxc.le.trans hce.le))
  have hC : IsLegalMove (SimpleGraph.pathGraph n) C := pathInterval_legal a x (hab.trans hbx)
  have hA : IsLegalMove (SimpleGraph.pathGraph n) A := pathInterval_legal d e (hdc.trans hce.le)
  have hp : reverseProfile [A, B, C] x = profileBlock L h + profileBlock A k +
      profileBlock T l := by
    change average A (average B (average C (pointMass x))) = _
    rw [average_pointMass C x hxC]
    profile_cases (dsimp only [C, B, A, D, T, L, h, u, l, k, q])
  have hq : reverseProfile [D, C] x = profileBlock L h + profileBlock A q +
      profileBlock T q := by
    change average D (average C (pointMass x)) = _
    rw [average_pointMass C x hxC]
    profile_cases (dsimp only [C, B, A, D, T, L, h, u, l, k, q])
  have hql : q ≤ l := mean_block_right_right_mono a x b c e hab hbx hxc.le hce.le h hh
  by_cases hdx : d ≤ x
  · let r := mean A u
    have hr : reverseProfile [A, C] x = profileBlock L h + profileBlock A r +
        profileBlock T h := by
      change average A (average C (pointMass x)) = _
      rw [average_pointMass C x hxC]
      profile_cases (dsimp only [C, B, A, D, T, L, h, u, l, k, q, r])
    have hlh : l ≤ h := by
      have hbne : B.Nonempty := ⟨b, Finset.mem_Icc.mpr ⟨le_rfl, hbx.trans hxc.le⟩⟩
      apply (div_le_iff₀ (by exact_mod_cast Finset.card_pos.mpr hbne)).mpr
      calc
        (∑ v ∈ B, u v) ≤ ∑ _v ∈ B, h := by
          apply Finset.sum_le_sum
          intro v _
          change (if v ∈ C then h else 0) ≤ h
          split_ifs <;> linarith
        _ = _ := by simp [mul_comm]
    have hval := run_le_max_of_profile_blocks w x [A, B, C] [D, C] [A, C]
      A T (profileBlock L h) k l q q r h hp hq hr hql hlh
    rcases le_max_iff.mp hval with hv | hv
    · exact ⟨[D, C], by simp [isLegal_cons, hD, hC], by simp, hv⟩
    · exact ⟨[A, C], by simp [isLegal_cons, hA, hC], by simp, hv⟩
  · let r := mean T u
    have hr : reverseProfile [T, C] x = profileBlock L h + profileBlock A 0 +
        profileBlock T r := by
      change average T (average C (pointMass x)) = _
      rw [average_pointMass C x hxC]
      profile_cases (dsimp only [C, B, A, D, T, L, h, u, l, k, q, r])
    have hlr : l ≤ r := by
      apply mean_profileBlock_antitone T B C ⟨b, Finset.mem_Ico.mpr ⟨le_rfl, hbd⟩⟩
      · intro v hv
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp hv).1, (Finset.mem_Ico.mp hv).2.le.trans hdc⟩
      · ext v
        simp only [T, B, C, Finset.mem_inter, Finset.mem_Ico, Finset.mem_Icc]
        omega
      · exact hh
    have hval := run_le_max_of_profile_blocks w x [A, B, C] [D, C] [T, C]
      A T (profileBlock L h) k l q q 0 r hp hq hr hql hlr
    rcases le_max_iff.mp hval with hv | hv
    · exact ⟨[D, C], by simp [isLegal_cons, hD, hC], by simp, hv⟩
    · exact ⟨[T, C], by simp [isLegal_cons, path_Ico_legal b d hbd, hC, T], by simp, hv⟩

private theorem mean_block_Ioc (a x e c : Fin n)
    (hae : a ≤ e) (hex : e ≤ x) (hxc : x ≤ c) (h : ℝ) :
    mean (Finset.Ioc e c) (profileBlock (Finset.Icc a x) h) =
      (x.val - e.val) * h / (c.val - e.val) := by
  have hi : Finset.Ioc e c ∩ Finset.Icc a x = Finset.Ioc e x := by
    ext v
    simp only [Finset.mem_inter, Finset.mem_Icc, Finset.mem_Ioc]
    constructor
    · exact fun hv => ⟨hv.1.1, hv.2.2⟩
    · exact fun hv => ⟨⟨hv.1, hv.2.trans hxc⟩, ⟨hae.trans hv.1.le, hv.2⟩⟩
  rw [mean_profileBlock, hi, Fin.card_Ioc, Fin.card_Ioc,
    Nat.cast_sub (show e.val ≤ x.val from hex),
    Nat.cast_sub (show e.val ≤ c.val from hex.trans hxc)]

/-- Arithmetic preparation for case 3: the expanded two-step candidate has no higher
right tail. After clearing positive denominators, the difference is a sum of nonnegative products. -/
private theorem outer_tail_bound (d a b e x c : Fin n)
    (hda : d ≤ a) (hab : a ≤ b) (hbe : b ≤ e) (hex : e < x) (hxc : x < c) :
    mean (Finset.Ioc e c) (profileBlock (Finset.Icc d x) (1 / (Finset.Icc d x).card)) ≤
      mean (Finset.Icc b c) (profileBlock (Finset.Icc a x) (1 / (Finset.Icc a x).card)) := by
  rw [mean_block_Ioc d x e c (hda.trans (hab.trans hbe)) hex.le hxc.le,
    mean_block_right a x b c hab (hbe.trans hex.le) hxc.le,
    card_Icc_real d x (hda.trans (hab.trans (hbe.trans hex.le))),
    card_Icc_real a x (hab.trans (hbe.trans hex.le))]
  simp only [mul_one_div, div_div]
  have hda' : (d.val : ℝ) ≤ a.val := by exact_mod_cast hda
  have hab' : (a.val : ℝ) ≤ b.val := by exact_mod_cast hab
  have hbe' : (b.val : ℝ) ≤ e.val := by exact_mod_cast hbe
  have hex' : (e.val : ℝ) < x.val := by exact_mod_cast hex
  have hxc' : (x.val : ℝ) < c.val := by exact_mod_cast hxc
  apply (div_le_div_iff₀ (mul_pos (by linarith) (by linarith))
    (mul_pos (by linarith) (by linarith))).mpr
  have h₁ := mul_nonneg (show 0 ≤ (a.val : ℝ) - d.val by linarith)
    (mul_nonneg (show 0 ≤ (x.val : ℝ) + 1 - b.val by linarith)
      (show 0 ≤ (c.val : ℝ) - e.val by linarith))
  have h₂ := mul_nonneg (show 0 ≤ (x.val : ℝ) + 1 - a.val by linarith)
    (mul_nonneg (show 0 ≤ (e.val : ℝ) + 1 - b.val by linarith)
      (show 0 ≤ (c.val : ℝ) - x.val by linarith))
  nlinarith

/-- Crossing case 3: the third reverse average extends left of the support and ends
left of the target. Compare a right-tail move followed by the expanded left move
with the right-tail move alone. -/
private theorem left_cross_outside_dominates (w : State (Fin n))
    (a b x c d e : Fin n) (hda : d ≤ a) (hab : a < b)
    (hbe : b ≤ e) (hex : e < x) (hxc : x < c) :
    ∃ τ, IsLegal (SimpleGraph.pathGraph n) τ ∧ τ.length ≤ 2 ∧
      run [Finset.Icc d e, Finset.Icc b c, Finset.Icc a x] w x ≤ run τ w x := by
  let C := Finset.Icc a x
  let B := Finset.Icc b c
  let A := Finset.Icc d e
  let D := Finset.Icc d x
  let T := Finset.Ioc e c
  let h : ℝ := 1 / C.card
  let u := profileBlock C h
  let l := mean B u
  let k := mean A (average B u)
  let hD : ℝ := 1 / D.card
  let q := mean T (profileBlock D hD)
  let r : ℝ := 1 / T.card
  have hxC : x ∈ C := Finset.mem_Icc.mpr ⟨hab.le.trans (hbe.trans hex.le), le_rfl⟩
  have hxD : x ∈ D := Finset.mem_Icc.mpr ⟨hda.trans (hab.le.trans (hbe.trans hex.le)), le_rfl⟩
  have hxT : x ∈ T := Finset.mem_Ioc.mpr ⟨hex, hxc.le⟩
  have legalD : IsLegalMove (SimpleGraph.pathGraph n) D :=
    pathInterval_legal d x (hda.trans (hab.le.trans (hbe.trans hex.le)))
  have legalT : IsLegalMove (SimpleGraph.pathGraph n) T := path_Ioc_legal e c (hex.trans hxc)
  have hp : reverseProfile [A, B, C] x = (0 : State (Fin n)) + profileBlock A k +
      profileBlock T l := by
    change average A (average B (average C (pointMass x))) = _
    rw [average_pointMass C x hxC]
    profile_cases (dsimp only [C, B, A, D, T, h, u, l, k, hD, q, r])
  have hq : reverseProfile [T, D] x = (0 : State (Fin n)) + profileBlock A hD +
      profileBlock T q := by
    change average T (average D (pointMass x)) = _
    rw [average_pointMass D x hxD]
    profile_cases (dsimp only [C, B, A, D, T, h, u, l, k, hD, q, r])
  have hr : reverseProfile [T] x = (0 : State (Fin n)) + profileBlock A 0 +
      profileBlock T r := by
    change average T (pointMass x) = _
    rw [average_pointMass T x hxT]
    funext v
    simp [profileBlock, r]
  have hql : q ≤ l := outer_tail_bound d a b e x c hda hab.le hbe hex hxc
  have hlr : l ≤ r := by
    have hu : u = reverseProfile [C] x := (average_pointMass C x hxC).symm
    have hlB : l ≤ 1 / B.card := by
      exact mean_le_inv_card_of_probability B u (hu ▸ reverseProfile_nonnegative [C] x)
        (hu ▸ reverseProfile_mass [C] x)
    apply hlB.trans
    apply div_le_div_of_nonneg_left zero_le_one
      (by exact_mod_cast Finset.card_pos.mpr ⟨x, hxT⟩)
    exact_mod_cast Finset.card_le_card (show T ⊆ B from fun v hv =>
      Finset.mem_Icc.mpr ⟨hbe.trans (Finset.mem_Ioc.mp hv).1.le, (Finset.mem_Ioc.mp hv).2⟩)
  have hval := run_le_max_of_profile_blocks w x [A, B, C] [T, D] [T]
    A T 0 k l hD q 0 r hp hq hr hql hlr
  rcases le_max_iff.mp hval with hv | hv
  · exact ⟨[T, D], by simp [isLegal_cons, legalT, legalD], by simp, hv⟩
  · exact ⟨[T], by simpa using legalT, by simp, hv⟩

/-!
## Geometric cases: containment and moves on one side

Remove the remaining degenerate configurations before combining all interval positions.
-/

/-- Containment case: the last set lies in the third-from-last set.
Deleting the middle or the last move preserves or improves the target value. -/
private theorem triple_contains_last (w : State (Fin n)) (x : Fin n)
    (A B C : Finset (Fin n)) (hA : IsLegalMove (SimpleGraph.pathGraph n) A)
    (hB : IsLegalMove (SimpleGraph.pathGraph n) B)
    (hC : IsLegalMove (SimpleGraph.pathGraph n) C)
    (hCA : C ⊆ A) (hxB : x ∈ B) (hxC : x ∈ C) :
    ∃ τ, IsLegal (SimpleGraph.pathGraph n) τ ∧ τ.length ≤ 2 ∧
      run [A, B, C] w x ≤ run τ w x := by
  have hval : run [A, B, C] w x ≤ max (run [A, C] w x) (run [A, B] w x) := by
    change average C (average B (average A w)) x ≤
      max (average C (average A w) x) (average B (average A w) x)
    rw [average_subset_absorb C A hCA, average_apply_mem A w (hCA hxC),
      average_apply_mem B (average A w) hxB, average_apply_mem C _ hxC]
    apply (div_le_iff₀ (by exact_mod_cast Finset.card_pos.mpr hC.1)).mpr
    calc
      (∑ v ∈ C, average B (average A w) v) ≤
          ∑ _v ∈ C, max (mean A w) (mean B (average A w)) := by
        apply Finset.sum_le_sum
        intro v hv
        by_cases hvB : v ∈ B
        · rw [average_apply_mem B _ hvB]
          exact le_max_right _ _
        · rw [average_apply_not_mem B _ hvB, average_apply_mem A w (hCA hv)]
          exact le_max_left _ _
      _ = _ := by simp [mul_comm]
  rcases le_max_iff.mp hval with hv | hv
  · exact ⟨[A, C], by simp [isLegal_cons, hA, hC], by simp, hv⟩
  · exact ⟨[A, B], by simp [isLegal_cons, hA, hB], by simp, hv⟩

/-- Two moves on the target's left are dominated by one interval average.
For overlapping incomparable intervals, compare their union with the rightmost tail. -/
private theorem left_pair_dominates (w : State (Fin n)) (a x d e : Fin n)
    (hax : a ≤ x) (hde : d ≤ e) (hex : e ≤ x) :
    ∃ R, IsLegalMove (SimpleGraph.pathGraph n) R ∧
      run [Finset.Icc d e, Finset.Icc a x] w x ≤ average R w x := by
  let A := Finset.Icc d e
  let C := Finset.Icc a x
  have hA : IsLegalMove (SimpleGraph.pathGraph n) A := pathInterval_legal d e hde
  have hC : IsLegalMove (SimpleGraph.pathGraph n) C := pathInterval_legal a x hax
  by_cases had : a ≤ d
  · have hAC : A ⊆ C := fun v hv => Finset.mem_Icc.mpr
      ⟨had.trans (Finset.mem_Icc.mp hv).1, (Finset.mem_Icc.mp hv).2.trans hex⟩
    exact ⟨C, hC, le_of_eq (congrFun (average_absorb_subset A C hAC w) x)⟩
  have hda : d < a := lt_of_not_ge had
  by_cases hxe : x ≤ e
  · have hCA : C ⊆ A := fun v hv => Finset.mem_Icc.mpr
      ⟨hda.le.trans (Finset.mem_Icc.mp hv).1, (Finset.mem_Icc.mp hv).2.trans hxe⟩
    exact ⟨A, hA, le_of_eq (congrFun (average_subset_absorb C A hCA w) x)⟩
  have hex' : e < x := lt_of_not_ge hxe
  by_cases hea : e < a
  · have hdis : Disjoint A C := by
      apply Finset.disjoint_left.mpr
      intro v hvA hvC
      have := Finset.mem_Icc.mp hvA
      have := Finset.mem_Icc.mp hvC
      omega
    have hxA : x ∉ A := by simp only [A, Finset.mem_Icc]; omega
    refine ⟨C, hC, le_of_eq ?_⟩
    change average C (average A w) x = _
    rw [average_comm_of_disjoint C A hdis.symm, average_apply_not_mem A _ hxA]
  have hae : a ≤ e := le_of_not_gt hea
  let U := Finset.Icc d x
  let T := Finset.Ioc e x
  let h : ℝ := 1 / C.card
  let k := mean A (profileBlock C h)
  let q : ℝ := 1 / U.card
  let r : ℝ := 1 / T.card
  have hxC : x ∈ C := Finset.mem_Icc.mpr ⟨hax, le_rfl⟩
  have hxU : x ∈ U := Finset.mem_Icc.mpr ⟨hde.trans hex, le_rfl⟩
  have hxT : x ∈ T := Finset.mem_Ioc.mpr ⟨hex', le_rfl⟩
  have hp : reverseProfile [A, C] x = (0 : State (Fin n)) + profileBlock A k +
      profileBlock T h := by
    change average A (average C (pointMass x)) = _
    rw [average_pointMass C x hxC]
    profile_cases (dsimp only [A, C, U, T, h, k, q, r])
  have hq : reverseProfile [U] x = (0 : State (Fin n)) + profileBlock A q +
      profileBlock T q := by
    change average U (pointMass x) = _
    rw [average_pointMass U x hxU]
    profile_cases (dsimp only [A, C, U, T, h, k, q, r])
  have hr : reverseProfile [T] x = (0 : State (Fin n)) + profileBlock A 0 +
      profileBlock T r := by
    change average T (pointMass x) = _
    rw [average_pointMass T x hxT]
    funext v
    simp [profileBlock, r]
  have hqh : q ≤ h := by
    apply div_le_div_of_nonneg_left zero_le_one
      (by exact_mod_cast Finset.card_pos.mpr ⟨x, hxC⟩)
    exact_mod_cast Finset.card_le_card (show C ⊆ U from fun v hv =>
      Finset.mem_Icc.mpr ⟨hda.le.trans (Finset.mem_Icc.mp hv).1, (Finset.mem_Icc.mp hv).2⟩)
  have hhr : h ≤ r := by
    apply div_le_div_of_nonneg_left zero_le_one
      (by exact_mod_cast Finset.card_pos.mpr ⟨x, hxT⟩)
    exact_mod_cast Finset.card_le_card (show T ⊆ C from fun v hv =>
      Finset.mem_Icc.mpr ⟨hae.trans (Finset.mem_Ioc.mp hv).1.le, (Finset.mem_Ioc.mp hv).2⟩)
  have hval := run_le_max_of_profile_blocks w x [A, C] [U] [T]
    A T 0 k h q q 0 r hp hq hr hqh hhr
  rcases le_max_iff.mp hval with hv | hv
  · exact ⟨U, pathInterval_legal d x (hde.trans hex), hv⟩
  · exact ⟨T, path_Ioc_legal e x hex', hv⟩

/-!
## Combine the cases and reflect

Obtain a two-move replacement for three moves when the final interval has the target as an endpoint.
-/

/-- Combine all positions of the third interval when the final two intervals cross
to the right. Remove disjoint and containment cases before applying the crossing comparisons. -/
private theorem normalized_triple_dominates (w : State (Fin n))
    (a b x c d e : Fin n) (hab : a < b) (hbx : b ≤ x)
    (hxc : x < c) (hde : d ≤ e) :
    ∃ τ, IsLegal (SimpleGraph.pathGraph n) τ ∧ τ.length ≤ 2 ∧
      run [Finset.Icc d e, Finset.Icc b c, Finset.Icc a x] w x ≤ run τ w x := by
  let A := Finset.Icc d e
  let B := Finset.Icc b c
  let C := Finset.Icc a x
  have hA : IsLegalMove (SimpleGraph.pathGraph n) A := pathInterval_legal d e hde
  have hB : IsLegalMove (SimpleGraph.pathGraph n) B := pathInterval_legal b c (hbx.trans hxc.le)
  have hC : IsLegalMove (SimpleGraph.pathGraph n) C := pathInterval_legal a x (hab.le.trans hbx)
  have deleteA (hAB : A ⊆ B) :
      run [A, B, C] w x ≤ run [B, C] w x := by
    change average C (average B (average A w)) x ≤ average C (average B w) x
    rw [average_absorb_subset A B hAB]
  have deleteB (hBA : B ⊆ A) :
      run [A, B, C] w x ≤ run [A, C] w x := by
    change average C (average B (average A w)) x ≤ average C (average A w) x
    rw [average_subset_absorb B A hBA]
  by_cases heb : e < b
  · have hdis : Disjoint A B := by
      apply Finset.disjoint_left.mpr
      intro v hvA hvB
      have := Finset.mem_Icc.mp hvA
      have := Finset.mem_Icc.mp hvB
      omega
    obtain ⟨R, hR, hv⟩ := left_pair_dominates (average B w) a x d e
      (hab.le.trans hbx) hde (heb.le.trans hbx)
    refine ⟨[B, R], by simp [isLegal_cons, hB, hR], by simp, ?_⟩
    change average C (average B (average A w)) x ≤ average R (average B w) x
    rw [average_comm_of_disjoint B A hdis.symm]
    exact hv
  by_cases hcd : c < d
  · have hdisB : Disjoint A B := by
      apply Finset.disjoint_left.mpr
      intro v hvA hvB
      have := Finset.mem_Icc.mp hvA
      have := Finset.mem_Icc.mp hvB
      omega
    have hdisC : Disjoint A C := by
      apply Finset.disjoint_left.mpr
      intro v hvA hvC
      have := Finset.mem_Icc.mp hvA
      have := Finset.mem_Icc.mp hvC
      omega
    have hxA : x ∉ A := by simp only [A, Finset.mem_Icc]; omega
    refine ⟨[B, C], by simp [isLegal_cons, hB, hC], by simp, ?_⟩
    change average C (average B (average A w)) x ≤ average C (average B w) x
    rw [average_comm_of_disjoint B A hdisB.symm,
      average_comm_of_disjoint C A hdisC.symm, average_apply_not_mem A _ hxA]
  have hbe : b ≤ e := le_of_not_gt heb
  have hdc : d ≤ c := le_of_not_gt hcd
  by_cases hbd : b ≤ d
  · by_cases hec : e ≤ c
    · have hAB : A ⊆ B := Finset.Icc_subset_Icc hbd hec
      exact ⟨[B, C], by simp [isLegal_cons, hB, hC], by simp, deleteA hAB⟩
    · by_cases hdb : d ≤ b
      · have hBA : B ⊆ A := Finset.Icc_subset_Icc hdb (le_of_not_ge hec)
        exact ⟨[A, C], by simp [isLegal_cons, hA, hC], by simp, deleteB hBA⟩
      · exact right_cross_dominates w a b x c d e hab.le hbx hxc
          (lt_of_not_ge hdb) hdc (lt_of_not_ge hec)
  · have hdb : d < b := lt_of_not_ge hbd
    by_cases hce : c ≤ e
    · have hBA : B ⊆ A := Finset.Icc_subset_Icc hdb.le hce
      exact ⟨[A, C], by simp [isLegal_cons, hA, hC], by simp, deleteB hBA⟩
    have hec : e < c := lt_of_not_ge hce
    by_cases had : a ≤ d
    · exact left_cross_inside_dominates w a b x c d e had hdb hbx hxc hbe hec
    have hda : d ≤ a := (lt_of_not_ge had).le
    by_cases hxe : x ≤ e
    · exact triple_contains_last w x A B C hA hB hC
        (Finset.Icc_subset_Icc hda hxe)
        (Finset.mem_Icc.mpr ⟨hbx, hxc.le⟩)
        (Finset.mem_Icc.mpr ⟨hab.le.trans hbx, le_rfl⟩)
    · exact left_cross_outside_dominates w a b x c d e hda hab hbe (lt_of_not_ge hxe) hxc

/-- When the target is the last interval's right endpoint, at most two moves dominate the last three. -/
private theorem right_endpoint_triple_dominates (w : State (Fin n)) (x a : Fin n)
    (hax : a ≤ x) (A B : Finset (Fin n))
    (hA : IsLegalMove (SimpleGraph.pathGraph n) A)
    (hB : IsLegalMove (SimpleGraph.pathGraph n) B) :
    ∃ τ, IsLegal (SimpleGraph.pathGraph n) τ ∧ τ.length ≤ 2 ∧
      run [A, B, Finset.Icc a x] w x ≤ run τ w x := by
  obtain ⟨b, c, hbc, rfl⟩ := (path_legal_iff_interval B).mp hB
  let C := Finset.Icc a x
  have hC : IsLegalMove (SimpleGraph.pathGraph n) C := pathInterval_legal a x hax
  by_cases hcx : c ≤ x
  · obtain ⟨R, hR, hv⟩ := left_pair_dominates (average A w) a x b c hax hbc hcx
    exact ⟨[A, R], by simp [isLegal_cons, hA, hR], by simp, hv⟩
  have hxc : x < c := lt_of_not_ge hcx
  by_cases hxb : x < b
  · have hdis : Disjoint (pathInterval b c) C := by
      apply Finset.disjoint_left.mpr
      intro v hvB hvC
      have := Finset.mem_Icc.mp hvB
      have := Finset.mem_Icc.mp hvC
      omega
    have hxB : x ∉ pathInterval b c := by simp only [pathInterval, Finset.mem_Icc]; omega
    refine ⟨[A, C], by simp [isLegal_cons, hA, hC], by simp, ?_⟩
    change average C (average (pathInterval b c) (average A w)) x ≤ average C (average A w) x
    rw [average_comm_of_disjoint C (pathInterval b c) hdis.symm,
      average_apply_not_mem (pathInterval b c) _ hxB]
  have hbx : b ≤ x := le_of_not_gt hxb
  by_cases hba : b ≤ a
  · have hCB : C ⊆ pathInterval b c := Finset.Icc_subset_Icc hba hxc.le
    refine ⟨[A, pathInterval b c], by simp [isLegal_cons, hA, hB], by simp, ?_⟩
    change average C (average (pathInterval b c) (average A w)) x ≤
      average (pathInterval b c) (average A w) x
    rw [average_subset_absorb C (pathInterval b c) hCB]
  obtain ⟨d, e, hde, rfl⟩ := (path_legal_iff_interval A).mp hA
  exact normalized_triple_dominates w a b x c d e (lt_of_not_ge hba) hbx hxc hde

private theorem map_interval_reflection (a b : Fin n) :
    (Finset.Icc a b).map (pathReflection n).toEquiv.toEmbedding =
      Finset.Icc b.rev a.rev := by
  ext v
  simp only [Finset.mem_map_equiv, Finset.mem_Icc]
  change (a ≤ v.rev ∧ v.rev ≤ b) ↔ (b.rev ≤ v ∧ v ≤ a.rev)
  simp only [Fin.le_rev_iff, Fin.rev_le_iff]
  exact and_comm

/-- Reflection supplies the left-endpoint case, transporting both the state and the full strategy. -/
private theorem endpoint_triple_dominates (w : State (Fin n)) (x a b : Fin n)
    (hab : a ≤ b) (hx : x = a ∨ x = b) (A B : Finset (Fin n))
    (hA : IsLegalMove (SimpleGraph.pathGraph n) A)
    (hB : IsLegalMove (SimpleGraph.pathGraph n) B) :
    ∃ τ, IsLegal (SimpleGraph.pathGraph n) τ ∧ τ.length ≤ 2 ∧
      run [A, B, Finset.Icc a b] w x ≤ run τ w x := by
  rcases hx with hxa | hxb
  · subst x
    let e := pathReflection n
    let f := Finset.map e.toEquiv.toEmbedding
    have hab' : e b ≤ e a := Fin.rev_le_rev.mpr hab
    obtain ⟨τ, hτ, hlen, hval⟩ := right_endpoint_triple_dominates
      (w ∘ e.symm) (e a) (e b) hab' (f A) (f B) (hA.map_iso e) (hB.map_iso e)
    have hmap : f (Finset.Icc a b) = Finset.Icc (e b) (e a) := map_interval_reflection a b
    have hinput : run [f A, f B, Finset.Icc (e b) (e a)] (w ∘ e.symm) (e a) =
        run [A, B, Finset.Icc a b] w a := by
      have hi := run_map_equiv e.toEquiv [A, B, Finset.Icc a b] w a
      change run [f A, f B, f (Finset.Icc a b)] (w ∘ e.symm) (e a) =
        run [A, B, Finset.Icc a b] w a at hi
      rw [hmap] at hi
      exact hi
    have hwback : (w ∘ e.symm) ∘ e = w := by funext v; simp
    have houtput := run_map_equiv e.symm.toEquiv τ (w ∘ e.symm) (e a)
    change run (τ.map (Finset.map e.symm.toEquiv.toEmbedding))
      ((w ∘ e.symm) ∘ e) (e.symm (e a)) = run τ (w ∘ e.symm) (e a) at houtput
    rw [hwback, e.symm_apply_apply] at houtput
    refine ⟨τ.map (Finset.map e.symm.toEquiv.toEmbedding), hτ.map_iso e.symm,
      by simpa only [List.length_map] using hlen, ?_⟩
    exact hinput.symm.le.trans (hval.trans_eq houtput.symm)
  · subst x
    exact right_endpoint_triple_dominates w b a hab A B hA hB

/-!
## Core theorem: a globally optimal path strategy needs at most two moves

Apply the replacement to a shortest optimal strategy; a length of at least three contradicts minimality.
-/

/-- Core two-step theorem via a globally shortest optimal strategy.

General attainment supplies such a strategy. If its length is at least three,
the split improvement forces the last interval to end at the target. The preceding
three-move comparisons then shorten it without reducing its globally optimal value. -/
theorem path_two_step_core (w : State (Fin n)) (hw : Nonnegative w) (x : Fin n) :
    ∃ σ, IsOptimal (SimpleGraph.pathGraph n) w x σ ∧ σ.length ≤ 2 := by
  obtain ⟨σ, hopt, hmin⟩ := optimalLength_spec (SimpleGraph.pathGraph n) w hw x
  refine ⟨σ, hopt, ?_⟩
  by_contra hlen
  have hthree : 3 ≤ σ.length := by omega
  obtain ⟨p, A, B, C, rfl⟩ : ∃ p A B C, σ = p ++ [A, B, C] := by
    have htail : (σ.drop (σ.length - 3)).length = 3 := by rw [List.length_drop]; omega
    obtain ⟨A, B, C, htail⟩ := List.length_eq_three.mp htail
    refine ⟨σ.take (σ.length - 3), A, B, C, ?_⟩
    rw [← htail]
    exact (List.take_append_drop _ _).symm
  have hA := hopt.1 A (by simp)
  have hB := hopt.1 B (by simp)
  have hC := hopt.1 C (by simp)
  obtain ⟨a, b, hab, rfl⟩ := (path_legal_iff_interval C).mp hC
  have hp : IsLegal (SimpleGraph.pathGraph n) p := ((isLegal_append _ _ _).mp hopt.1).1
  have hoptEnd : IsOptimal (SimpleGraph.pathGraph n) w x
      ((p ++ [A, B]) ++ [pathInterval a b]) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using hopt
  have hx : x = a ∨ x = b := by
    rcases optimal_path_last_endpoint_or_prefix w x a b (p ++ [A, B]) hoptEnd with ha | hb | hpre
    · exact Or.inl ha
    · exact Or.inr hb
    · have hle := optimalLength_le (SimpleGraph.pathGraph n) w hw x (p ++ [A, B]) hpre
      simp only [List.length_append, List.length_cons, List.length_nil] at hle hmin
      omega
  obtain ⟨τ, hτ, hτlen, hdom⟩ := endpoint_triple_dominates (run p w) x a b hab hx A B hA hB
  have hdom' : run (p ++ [A, B, pathInterval a b]) w x ≤ run (p ++ τ) w x := by
    simpa only [run_append, pathInterval] using hdom
  have hopt' : IsOptimal (SimpleGraph.pathGraph n) w x (p ++ τ) :=
    ⟨(isLegal_append _ _ _).mpr ⟨hp, hτ⟩, fun ρ hρ => (hopt.2 ρ hρ).trans hdom'⟩
  have hle := optimalLength_le (SimpleGraph.pathGraph n) w hw x (p ++ τ) hopt'
  simp only [List.length_append, List.length_cons, List.length_nil] at hle hmin
  omega

end WaterTransport
