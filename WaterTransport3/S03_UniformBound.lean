import WaterTransport3.S02_LocalGeometry
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Paper 3, Section 2: window contraction and a uniform length bound

Window support graphs retain the full vertex set, including unused isolated
vertices. The final theorem applies to every finite simple graph.

Proof route: shorten disconnected windows (Lemma 2.1); estimate connected-window
energy loss and mixing (Lemmas 2.2-2.3); replace mixed blocks using local geometry;
induct on vertex count and strategy length (Theorem 1.1); derive explicit growth,
rational-polytope structure, and short optimal strategies (Corollary 1.2).
-/

namespace WaterTransport.Paper3

variable {V : Type*} [Fintype V] [DecidableEq V]

/-!
## Definition: the support graph of a strategy window

Retain all vertices and only edges whose endpoints occur together in some selected set.
-/

/-- Edges of G whose two endpoints occur together in at least one move; unused vertices remain present. -/
def supportGraph (G : SimpleGraph V) (σ : Strategy V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ ∃ S ∈ σ, u ∈ S ∧ v ∈ S
  symm := by
    constructor
    rintro u v ⟨h, S, hS, hu, hv⟩
    exact ⟨h.symm, S, hS, hv, hu⟩
  loopless := ⟨by intro v h; exact G.loopless.irrefl v h.1⟩

/-!
## Preparation for disconnected windows: lift, restrict, and regroup

Lift component operators and their convex decompositions, and commute moves on disjoint components.
-/

private noncomputable def liftMatrix (C : Finset V) (M : Matrix C C ℝ) : Matrix V V ℝ :=
  fun i j => if hi : i ∈ C then if hj : j ∈ C then M ⟨i, hi⟩ ⟨j, hj⟩ else 0
    else if i = j then 1 else 0

private lemma lift_strategyMatrix (C : Finset V) (τ : Strategy C) :
    strategyMatrix (τ.map (Finset.map (Function.Embedding.subtype (· ∈ C)))) =
      liftMatrix C (strategyMatrix τ) := by
  classical
  ext i j
  unfold liftMatrix strategyMatrix
  by_cases hi : i ∈ C
  · change run (τ.map (Finset.map (Function.Embedding.subtype (· ∈ C)))) (pointMass j) i = _
    trans run τ (pointMass j ∘ Function.Embedding.subtype (· ∈ C)) ⟨i, hi⟩
    · exact run_map_embedding (Function.Embedding.subtype (· ∈ C)) τ (pointMass j) ⟨i, hi⟩
    by_cases hj : j ∈ C
    · have hpoint : pointMass j ∘ (Function.Embedding.subtype (· ∈ C)) = pointMass (⟨j, hj⟩ : C) := by
        ext v
        simp [pointMass, Subtype.ext_iff]
      rw [hpoint]
      simp [liftMatrix, hi, hj, strategyMatrix]
    · have hpoint : pointMass j ∘ (Function.Embedding.subtype (· ∈ C)) = (fun _ => (0 : ℝ)) := by
        ext v
        have hne : v.val ≠ j := fun h => hj (h ▸ v.property)
        simp [pointMass, hne]
      rw [hpoint]
      have hz (σ : Strategy C) : run σ (fun _ => (0 : ℝ)) = fun _ => 0 := by
        induction σ with
        | nil => rfl
        | cons T σ ih => rw [run_cons, average_const, ih]
      simp [hz, liftMatrix, hi, hj]
  · have hout := run_map_outside (Function.Embedding.subtype (· ∈ C)) τ (pointMass j) i (by
      rintro ⟨v, rfl⟩; exact hi v.property)
    simpa [strategyMatrix, liftMatrix, hi, pointMass] using hout

private lemma legal_lift (G : SimpleGraph V) (C : Finset V) (T : Finset C)
    (hT : IsLegalMove (G.induce (C : Set V)) T) :
    IsLegalMove G (T.map (Function.Embedding.subtype (· ∈ C))) := by
  let e := Function.Embedding.subtype (· ∈ C)
  refine ⟨hT.1.map, ?_⟩
  let f : (G.induce (C : Set V)).induce (T : Set C) →g G.induce (T.map e : Set V) :=
    { toFun := fun x => ⟨x.val.val, Finset.mem_map.mpr ⟨x.val, x.property, rfl⟩⟩
      map_rel' := fun h => h }
  apply hT.2.map f
  intro y
  obtain ⟨u, hu, heq⟩ := Finset.mem_map.mp y.property
  exact ⟨⟨u, hu⟩, Subtype.ext heq⟩

private lemma lift_polytope (G : SimpleGraph V) (C : Finset V) (k : ℕ)
    (M : Matrix C C ℝ) (hM : M ∈ operatorPolytope (G.induce (C : Set V)) k) :
    liftMatrix C M ∈ operatorPolytope G k := by
  classical
  have hconv : Convex ℝ ((liftMatrix C) ⁻¹' operatorPolytope G k) := by
    intro A hA B hB a b ha hb hab
    change liftMatrix C (a • A + b • B) ∈ operatorPolytope G k
    have heq : liftMatrix C (a • A + b • B) = a • liftMatrix C A + b • liftMatrix C B := by
      ext i j
      simp only [liftMatrix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      split_ifs <;> simp_all
    rw [heq]
    exact (convex_convexHull ℝ _) hA hB ha hb hab
  apply convexHull_min (t := (liftMatrix C) ⁻¹' operatorPolytope G k) ?_ hconv hM
  rintro A ⟨τ, hτ, hlen, rfl⟩
  change liftMatrix C (strategyMatrix τ) ∈ operatorPolytope G k
  rw [← lift_strategyMatrix]
  apply strategyMatrix_mem_polytope G _ _ (by simpa using hlen)
  intro T hT
  obtain ⟨U, hU, rfl⟩ := List.mem_map.mp hT
  exact legal_lift G C U (hτ U hU)

private lemma polytope_mul (G : SimpleGraph V) (a b : ℕ) (A B : Matrix V V ℝ)
    (hA : A ∈ operatorPolytope G a) (hB : B ∈ operatorPolytope G b) :
    B * A ∈ operatorPolytope G (a + b) := by
  have hbase (τ : Strategy V) (hτ : IsLegal G τ) (hlenτ : τ.length ≤ a) :
      B * strategyMatrix τ ∈ operatorPolytope G (a + b) := by
    apply convexHull_min (t := (LinearMap.mulRight ℝ (strategyMatrix τ)) ⁻¹' operatorPolytope G (a + b)) ?_
      ((convex_convexHull ℝ _).linear_preimage _) hB
    rintro M ⟨σ, hσ, hlenσ, rfl⟩
    change strategyMatrix σ * strategyMatrix τ ∈ operatorPolytope G (a + b)
    rw [← strategyMatrix_append]
    exact strategyMatrix_mem_polytope G _ ((isLegal_append _ _ _).mpr ⟨hτ, hσ⟩) (by simp; omega)
  apply convexHull_min (t := (LinearMap.mulLeft ℝ B) ⁻¹' operatorPolytope G (a + b)) ?_
    ((convex_convexHull ℝ _).linear_preimage _) hA
  rintro M ⟨τ, hτ, hlen, rfl⟩
  exact hbase τ hτ hlen

private lemma legal_restrict (G : SimpleGraph V) (C T : Finset V)
    (hT : IsLegalMove G T) (hsub : T ⊆ C) :
    IsLegalMove (G.induce (C : Set V)) (T.subtype (· ∈ C)) := by
  classical
  obtain ⟨v, hv⟩ := hT.1
  refine ⟨⟨⟨v, hsub hv⟩, by simpa using hv⟩, ?_⟩
  let f : G.induce (T : Set V) →g
      (G.induce (C : Set V)).induce (T.subtype (· ∈ C) : Set C) :=
    { toFun := fun x => ⟨⟨x.val, hsub x.property⟩, by simpa using x.property⟩
      map_rel' := fun h => h }
  apply hT.2.map f
  intro y
  refine ⟨⟨y.val.val, Finset.mem_subtype.mp y.property⟩, ?_⟩
  exact Subtype.ext (Subtype.ext rfl)

private lemma smaller_graph_bound {U : Type*} [Fintype U] [DecidableEq U]
    (G : SimpleGraph U) (k : ℕ)
    (hfin : ∀ H : SimpleGraph (Fin (Fintype.card U)), ∀ σ : Strategy (Fin (Fintype.card U)),
      IsLegal H σ → strategyMatrix σ ∈ operatorPolytope H k)
    (σ : Strategy U) (hσ : IsLegal G σ) : strategyMatrix σ ∈ operatorPolytope G k := by
  let e := Fintype.equivFin U
  let H := G.comap e.symm
  let iso : G ≃g H := { toEquiv := e, map_rel_iff' := by intro a b; simp [H] }
  have h := hfin H (σ.map (Finset.map e.toEmbedding)) (hσ.map_iso iso)
  have hback := operatorPolytope_map_iso iso.symm k h
  rw [strategyMatrix_reindex] at hback
  have heq : Matrix.reindex iso.symm.toEquiv iso.symm.toEquiv
      (Matrix.reindex e e (strategyMatrix σ)) = strategyMatrix σ := by
    ext i j
    change strategyMatrix σ (e.symm (e i)) (e.symm (e j)) = strategyMatrix σ i j
    simp
  rwa [heq] at hback

private lemma strategy_on_subset_bound (G : SimpleGraph V) (C : Finset V) (k : ℕ)
    (hfin : ∀ H : SimpleGraph (Fin C.card), ∀ σ : Strategy (Fin C.card),
      IsLegal H σ → strategyMatrix σ ∈ operatorPolytope H k)
    (σ : Strategy V) (hσ : IsLegal G σ) (hsub : ∀ T ∈ σ, T ⊆ C) :
    strategyMatrix σ ∈ operatorPolytope G k := by
  classical
  let τ : Strategy C := σ.map (Finset.subtype (· ∈ C))
  have hτ : IsLegal (G.induce (C : Set V)) τ := by
    intro S hS
    obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hS
    exact legal_restrict G C T (hσ T hT) (hsub T hT)
  have hbound := smaller_graph_bound (G.induce (C : Set V)) k (by
    have hcard : Fintype.card (C : Set V) = C.card :=
      Fintype.card_of_subtype C (fun _ => Iff.rfl)
    rw [hcard]
    exact hfin) τ hτ
  have h := lift_polytope G C k (strategyMatrix τ) hbound
  rw [← lift_strategyMatrix] at h
  have heq : τ.map (Finset.map (Function.Embedding.subtype (· ∈ C))) = σ := by
    simp only [τ, List.map_map]
    conv_rhs => rw [← List.map_id σ]
    apply List.map_congr_left
    intro T hT
    exact Finset.subtype_map_of_mem (fun v hv => hsub T hT hv)
  rwa [heq] at h

private lemma run_commutes_with_disjoint (τ : Strategy V) (S : Finset V)
    (hdisj : ∀ T ∈ τ, Disjoint S T) (w : State V) :
    run τ (average S w) = average S (run τ w) := by
  induction τ generalizing w with
  | nil => rfl
  | cons T τ ih =>
    rw [run_cons, average_comm_of_disjoint T S (hdisj T (by simp)).symm,
      ih (fun U hU => hdisj U (by simp [hU])), run_cons]

/-- Group moves by components using only commutations of disjoint averages, preserving the full strategy operator. -/
private lemma run_partition (C : Finset V) (σ : Strategy V)
    (hside : ∀ T ∈ σ, T ⊆ C ∨ T ⊆ Finset.univ \ C) (w : State V) :
    run σ w = run (σ.filter (fun T => ¬ T ⊆ C)) (run (σ.filter (fun T => T ⊆ C)) w) := by
  classical
  induction σ generalizing w with
  | nil => rfl
  | cons S σ ih =>
    have htail : ∀ T ∈ σ, T ⊆ C ∨ T ⊆ Finset.univ \ C := fun T hT => hside T (by simp [hT])
    by_cases hS : S ⊆ C
    · simpa [List.filter_cons, hS, run_cons] using ih htail (average S w)
    · have hSC := (hside S (by simp)).resolve_left hS
      have hdisj : ∀ T ∈ σ.filter (fun T => T ⊆ C), Disjoint S T := by
        intro T hT
        have ht := List.mem_filter.mp hT
        have hTC : T ⊆ C := of_decide_eq_true ht.2
        apply Finset.disjoint_left.mpr
        intro v hvS hvT
        exact (Finset.mem_sdiff.mp (hSC hvS)).2 (hTC hvT)
      have hcomm := run_commutes_with_disjoint (σ.filter (fun T => T ⊆ C)) S hdisj w
      simp only [List.filter_cons]
      simp [hS, run_cons]
      rw [ih htail, hcomm]
      simp only [decide_not]

private lemma disconnected_partition (G : SimpleGraph V) (σ : Strategy V)
    (hσ : IsLegal G σ) [Nonempty V] (hd : ¬ (supportGraph G σ).Connected) :
    ∃ C : Finset V, C.Nonempty ∧ (Finset.univ \ C).Nonempty ∧
      ∀ T ∈ σ, T ⊆ C ∨ T ⊆ Finset.univ \ C := by
  classical
  let H := supportGraph G σ
  have hp : ¬ H.Preconnected := fun h => hd ⟨h⟩
  change ¬ ∀ u v, H.Reachable u v at hp
  push Not at hp
  obtain ⟨a, b, hab⟩ := hp
  let C := {v | H.Reachable a v}.toFinset
  refine ⟨C, ⟨a, by simp [C]⟩, ⟨b, by simpa [C] using hab⟩, ?_⟩
  intro T hT
  obtain ⟨u, hu⟩ := (hσ T hT).1
  have hconn : (H.induce (T : Set V)).Connected :=
    (hσ T hT).2.mono (show G.induce (T : Set V) ≤ H.induce (T : Set V) from
      fun x y h => ⟨h, T, hT, x.property, y.property⟩)
  have hr (v : V) (hv : v ∈ T) : H.Reachable u v :=
    (hconn ⟨u, hu⟩ ⟨v, hv⟩).map (SimpleGraph.Embedding.induce (T : Set V)).toHom
  by_cases huC : u ∈ C
  · left
    intro v hv
    have ha : H.Reachable a u := by simpa [C] using huC
    simpa [C] using ha.trans (hr v hv)
  · right
    intro v hv
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, C, Set.mem_toFinset, Set.mem_setOf_eq]
    intro ha
    apply huC
    simpa [C] using ha.trans (hr v hv).symm

private lemma split_length_bound (n : ℕ) (l : ℕ → ℕ) (hl1 : l 1 = 0)
    (hl : ∀ j, 2 ≤ j → j < n → 2 * l (j - 1) ≤ l j)
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a + b = n) :
    l a + l b ≤ l (n - 1) := by
  have mono (i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) : j < n → l i ≤ l j := by
    induction j, hij using Nat.le_induction with
    | base => exact fun _ => le_rfl
    | succ j hj ih =>
      intro hjn
      have hstep := hl (j + 1) (by omega) hjn
      have hprev := ih (by omega)
      simp only [Nat.add_sub_cancel] at hstep
      omega
  by_cases ha1 : a = 1
  · subst a
    simpa [hl1, show n - 1 = b by omega]
  by_cases hb1 : b = 1
  · subst b
    simpa [hl1, show n - 1 = a by omega]
  have hmax : max a b + 1 ≤ n - 1 := by omega
  have hma := mono a (max a b) ha (le_max_left _ _) (by omega)
  have hmb := mono b (max a b) hb (le_max_right _ _) (by omega)
  have hstep := hl (max a b + 1) (by omega) (by omega)
  have hfinal := mono (max a b + 1) (n - 1) (by omega) hmax (by omega)
  simp only [Nat.add_sub_cancel] at hstep
  omega

/-!
## Lemma 2.1: shorten a disconnected window

Apply smaller-graph bounds to the component partition and combine the replacements.
-/

/-- Lemma 2.1: shorten a disconnected window using the stated induction hypothesis
on smaller graphs. No attainment hypothesis for the current graph is needed. -/
theorem disconnected_window_shortening (G : SimpleGraph V) (hn : 3 ≤ Fintype.card V)
    (l : ℕ → ℕ) (hl1 : l 1 = 0)
    (hl : ∀ j, 2 ≤ j → j < Fintype.card V → 2 * l (j - 1) ≤ l j)
    (hsmall : ∀ j, j < Fintype.card V → ∀ H : SimpleGraph (Fin j),
      ∀ τ : Strategy (Fin j), IsLegal H τ → strategyMatrix τ ∈ operatorPolytope H (l j))
    (σ : Strategy V) (hσ : IsLegal G σ) (hd : ¬ (supportGraph G σ).Connected) :
    strategyMatrix σ ∈ operatorPolytope G (l (Fintype.card V - 1)) := by
  classical
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨C, hC, hD, hside⟩ := disconnected_partition G σ hσ hd
  let D := Finset.univ \ C
  let α := σ.filter (fun T => T ⊆ C)
  let β := σ.filter (fun T => ¬ T ⊆ C)
  have hα : IsLegal G α := fun T hT => hσ T (List.mem_filter.mp hT).1
  have hβ : IsLegal G β := fun T hT => hσ T (List.mem_filter.mp hT).1
  have hαsub : ∀ T ∈ α, T ⊆ C := fun T hT => of_decide_eq_true (List.mem_filter.mp hT).2
  have hβsub : ∀ T ∈ β, T ⊆ D := by
    intro T hT
    obtain ⟨hmem, hnot⟩ := List.mem_filter.mp hT
    exact (hside T hmem).resolve_left (of_decide_eq_true hnot)
  have hcards : C.card + D.card = Fintype.card V := by
    dsimp [D]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ C), Finset.card_univ]
    exact Nat.add_sub_of_le C.card_le_univ
  have hCpos := hC.card_pos
  have hDpos : 0 < D.card := hD.card_pos
  have hCsmall : C.card < Fintype.card V := by omega
  have hDsmall : D.card < Fintype.card V := by omega
  have hA := strategy_on_subset_bound G C (l C.card) (hsmall C.card hCsmall) α hα hαsub
  have hB := strategy_on_subset_bound G D (l D.card) (hsmall D.card hDsmall) β hβ hβsub
  have hmul := polytope_mul G (l C.card) (l D.card) _ _ hA hB
  have heq : strategyMatrix σ = strategyMatrix β * strategyMatrix α := by
    rw [← strategyMatrix_append]
    ext i j
    change run σ (pointMass j) i = run (α ++ β) (pointMass j) i
    rw [run_append]
    exact congrFun (run_partition C σ hside (pointMass j)) i
  rw [heq]
  exact operatorPolytope_mono G (split_length_bound _ l hl1 hl C.card D.card hCpos hDpos hcards) hmul

/-!
## Preparation for connected windows: first-crossing energy loss

Sort initial levels, track which gaps have been crossed, and charge each new crossing to an energy drop.
-/

private lemma pair_energy_drop (S : Finset V) (w : State V) (i j : V)
    (hi : i ∈ S) (hj : j ∈ S) :
    (w j - w i) ^ 2 ≤ 2 * (energy w - energy (average S w)) := by
  rw [energy_drop]
  by_cases hij : i = j
  · subst j
    simp only [sub_self, zero_pow (by decide : 2 ≠ 0)]
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun v _ => sq_nonneg (w v - mean S w)))
  have hpair : (w i - mean S w) ^ 2 + (w j - mean S w) ^ 2 ≤
      ∑ v ∈ S, (w v - mean S w) ^ 2 := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg
      (show ({i, j} : Finset V) ⊆ S by intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv; rcases hv with rfl | rfl <;> assumption)
      (fun v _ _ => sq_nonneg (w v - mean S w))
    simpa [hij] using h
  nlinarith [sq_nonneg ((w i - mean S w) + (w j - mean S w))]

private def Crosses {m : ℕ} (S : Finset (Fin (m + 1))) (p : Fin m) : Prop :=
  ∃ i ∈ S, ∃ j ∈ S, i ≤ p.castSucc ∧ p.castSucc < j

private noncomputable def crossed {m : ℕ} (σ : Strategy (Fin (m + 1))) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun p => ∃ S ∈ σ, Crosses S p

private lemma uncut_bounds (m : ℕ) (w : State (Fin (m + 1))) (hw : Monotone w)
    (σ : Strategy (Fin (m + 1))) (p : Fin m) (hp : p ∉ crossed σ) :
    (∀ i, i ≤ p.castSucc → run σ w i ≤ w p.castSucc) ∧
    (∀ j, p.castSucc < j → w p.succ ≤ run σ w j) := by
  classical
  induction σ using List.reverseRecOn with
  | nil =>
    constructor
    · exact fun i hi => hw hi
    · intro j hj
      exact hw (by simpa [Fin.le_def, Fin.lt_def] using hj)
  | append_singleton σ S ih =>
    have hprev : p ∉ crossed σ := by
      simp only [crossed, Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and] at hp ⊢
      exact fun T hT => hp T (by simp [hT])
    have hS : ¬ Crosses S p := by
      intro h
      apply hp
      simp only [crossed, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨S, by simp, h⟩
    obtain ⟨hlow, hhigh⟩ := ih hprev
    rw [run_append]
    change (∀ i, i ≤ p.castSucc → average S (run σ w) i ≤ w p.castSucc) ∧
      (∀ j, p.castSucc < j → w p.succ ≤ average S (run σ w) j)
    constructor
    · intro i hi
      by_cases hiS : i ∈ S
      · rw [average_apply_mem S _ hiS]
        have hbound : ∀ j ∈ S, run σ w j ≤ w p.castSucc := by
          intro j hj
          apply hlow j
          by_contra hn
          exact hS ⟨i, hiS, j, hj, hi, lt_of_not_ge hn⟩
        simpa only [Finset.expect_eq_sum_div_card, mean] using Finset.expect_le ⟨i, hiS⟩ hbound
      · rw [average_apply_not_mem S _ hiS]
        exact hlow i hi
    · intro j hj
      by_cases hjS : j ∈ S
      · rw [average_apply_mem S _ hjS]
        have hbound : ∀ i ∈ S, w p.succ ≤ run σ w i := by
          intro i hi
          apply hhigh i
          by_contra hn
          exact hS ⟨i, hi, j, hjS, le_of_not_gt hn, hj⟩
        simpa only [Finset.expect_eq_sum_div_card, mean] using Finset.le_expect ⟨j, hjS⟩ hbound
      · rw [average_apply_not_mem S _ hjS]
        exact hhigh j hj

private lemma gaps_between (m : ℕ) (w : State (Fin (m + 1))) (hw : Monotone w)
    (C : Finset (Fin m)) (hC : C.Nonempty) :
    ∑ p ∈ C, (w p.succ - w p.castSucc) ^ 2 ≤
      (w (C.max' hC).succ - w (C.min' hC).castSucc) ^ 2 := by
  have hnonneg (p : Fin m) : 0 ≤ w p.succ - w p.castSucc :=
    sub_nonneg.mpr (hw (by simp [Fin.le_def]))
  have hsub : C ⊆ Finset.Icc (C.min' hC) (C.max' hC) := by
    intro p hp
    exact Finset.mem_Icc.mpr ⟨C.min'_le p hp, C.le_max' p hp⟩
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => hnonneg p)
  rw [Fin.sum_Icc_sub (Finset.min'_le_max' C hC) w] at hsum
  have hsq := Finset.sum_sq_le_sq_sum_of_nonneg (s := C) (fun p _ => hnonneg p)
  have htotal : 0 ≤ ∑ p ∈ C, (w p.succ - w p.castSucc) := Finset.sum_nonneg fun p _ => hnonneg p
  exact hsq.trans (pow_le_pow_left₀ htotal hsum 2)

/-- One average pays for all initial sorted gaps crossed for the first time at
that step. Variances at the extreme newly crossed endpoints control their squared sum. -/
private lemma first_crossing_energy (m : ℕ) (w : State (Fin (m + 1))) (hw : Monotone w)
    (σ : Strategy (Fin (m + 1))) :
    (∑ p ∈ crossed σ, (w p.succ - w p.castSucc) ^ 2) ≤
      2 * (energy w - energy (run σ w)) := by
  classical
  induction σ using List.reverseRecOn with
  | nil => simp [crossed, run]
  | append_singleton σ S ih =>
    let C := Finset.univ.filter fun p : Fin m => p ∉ crossed σ ∧ Crosses S p
    have hnew : crossed (σ ++ [S]) = crossed σ ∪ C := by
      ext p
      by_cases hp : p ∈ crossed σ <;> simp [crossed, C] at hp ⊢ <;> aesop
    have hdisj : Disjoint (crossed σ) C := by
      apply Finset.disjoint_left.mpr
      intro p hp hC
      exact (Finset.mem_filter.mp hC).2.1 hp
    have hstep : (∑ p ∈ C, (w p.succ - w p.castSucc) ^ 2) ≤
        2 * (energy (run σ w) - energy (average S (run σ w))) := by
      by_cases hC : C.Nonempty
      · let p := C.min' hC
        let q := C.max' hC
        have hp : p ∉ crossed σ ∧ Crosses S p := (Finset.mem_filter.mp (C.min'_mem hC)).2
        have hq : q ∉ crossed σ ∧ Crosses S q := (Finset.mem_filter.mp (C.max'_mem hC)).2
        obtain ⟨i, hiS, _, _, hip, _⟩ := hp.2
        obtain ⟨_, _, j, hjS, _, hqj⟩ := hq.2
        have hi := (uncut_bounds m w hw σ p hp.1).1 i hip
        have hj := (uncut_bounds m w hw σ q hq.1).2 j hqj
        have hrange : 0 ≤ w q.succ - w p.castSucc := sub_nonneg.mpr (hw (by
          have h := Finset.min'_le_max' C hC
          simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ] at h ⊢
          omega))
        calc
          _ ≤ (w q.succ - w p.castSucc) ^ 2 := gaps_between m w hw C hC
          _ ≤ (run σ w j - run σ w i) ^ 2 := pow_le_pow_left₀ hrange (by linarith) 2
          _ ≤ _ := pair_energy_drop S (run σ w) i j hiS hjS
      · rw [Finset.not_nonempty_iff_eq_empty.mp hC, Finset.sum_empty]
        have h := energy_average_le S (run σ w)
        linarith
    rw [hnew, Finset.sum_union hdisj, run_append]
    change _ ≤ 2 * (energy w - energy (average S (run σ w)))
    linarith

private lemma connected_crossed (m : ℕ) (G : SimpleGraph (Fin (m + 1)))
    (σ : Strategy (Fin (m + 1))) (hc : (supportGraph G σ).Connected) :
    crossed σ = Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro p
  by_contra hp
  have hstep {u v : Fin (m + 1)} (h : (supportGraph G σ).Adj u v)
      (hu : u ≤ p.castSucc) : v ≤ p.castSucc := by
    by_contra hv
    obtain ⟨_, S, hS, huS, hvS⟩ := h
    apply hp
    simp only [crossed, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨S, hS, u, huS, v, hvS, hu, lt_of_not_ge hv⟩
  have hwalk {u v : Fin (m + 1)} (q : (supportGraph G σ).Walk u v) :
      u ≤ p.castSucc → v ≤ p.castSucc := by
    induction q with
    | nil => exact id
    | cons h q ih => exact fun hu => ih (hstep h hu)
  obtain ⟨q⟩ := hc (0 : Fin (m + 1)) (Fin.last m)
  have h := hwalk q (Fin.zero_le _)
  have hp' := p.isLt
  simp only [Fin.le_def, Fin.val_last, Fin.val_castSucc] at h
  omega

private lemma centered_energy_difference (σ : Strategy V) (w : State V) :
    centeredEnergy w - centeredEnergy (run σ w) = energy w - energy (run σ w) := by
  have hf (x : State V) : centeredEnergy x = energy x -
      2 * mean Finset.univ x * mass x + (Fintype.card V : ℝ) * (mean Finset.univ x) ^ 2 := by
    simp only [centeredEnergy, energy, Pi.sub_apply, sub_sq, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mass]
    ring
  have hm : mean Finset.univ (run σ w) = mean Finset.univ w := by
    unfold mean
    rw [show (∑ v, run σ w v) = ∑ v, w v from run_mass σ w]
  rw [hf, hf, hm, run_mass]
  ring

private lemma sorted_window_energy (m : ℕ) (G : SimpleGraph (Fin (m + 1)))
    (σ : Strategy (Fin (m + 1))) (hc : (supportGraph G σ).Connected)
    (w : State (Fin (m + 1))) (hw : Monotone w) :
    centeredEnergy (run σ w) ≤ (1 - 4 / (((m + 1 : ℕ) : ℝ) ^ 2)) * centeredEnergy w := by
  have hcredit := first_crossing_energy m w hw σ
  rw [connected_crossed m G σ hc, ← centered_energy_difference] at hcredit
  have hpoincare := path_variance_le_gap_energy m w
  have hsq (p : Fin m) : (w p.succ - w p.castSucc) ^ 2 = (w p.castSucc - w p.succ) ^ 2 := by ring
  simp_rw [hsq] at hcredit
  have hn2 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) ^ 2 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hcredit hn2.le
  have htotal : 4 * centeredEnergy w ≤ ((m + 1 : ℕ) : ℝ) ^ 2 *
      (centeredEnergy w - centeredEnergy (run σ w)) := by nlinarith
  rw [sub_mul, one_mul, div_mul_eq_mul_div]
  have h : 4 * centeredEnergy w / ((m + 1 : ℕ) : ℝ) ^ 2 ≤
      centeredEnergy w - centeredEnergy (run σ w) :=
    (div_le_iff₀ hn2).mpr (by simpa only [mul_comm] using htotal)
  linarith

private lemma centered_energy_reindex {U : Type*} [Fintype U] [DecidableEq U]
    (e : V ≃ U) (w : State V) : centeredEnergy (w ∘ e.symm) = centeredEnergy w := by
  have hm : mean Finset.univ (w ∘ e.symm) = mean Finset.univ w := by
    unfold mean
    rw [Finset.card_univ, Finset.card_univ, Fintype.card_congr e]
    congr 1
    exact e.symm.sum_comp w
  simp only [centeredEnergy, energy, Pi.sub_apply, hm, Function.comp_apply]
  exact e.symm.sum_comp (fun v => (w v - mean Finset.univ w) ^ 2)

private lemma support_connected_map {U : Type*} [Fintype U] [DecidableEq U]
    {G : SimpleGraph V} {H : SimpleGraph U} (e : G ≃g H) (σ : Strategy V)
    (hc : (supportGraph G σ).Connected) :
    (supportGraph H (σ.map (Finset.map e.toEquiv.toEmbedding))).Connected := by
  let f : supportGraph G σ →g supportGraph H (σ.map (Finset.map e.toEquiv.toEmbedding)) :=
    { toFun := e
      map_rel' := by
        intro u v h
        obtain ⟨huv, S, hS, hu, hv⟩ := h
        exact ⟨e.map_rel_iff.mpr huv, S.map e.toEquiv.toEmbedding,
          List.mem_map.mpr ⟨S, hS, rfl⟩,
          Finset.mem_map.mpr ⟨u, hu, rfl⟩, Finset.mem_map.mpr ⟨v, hv, rfl⟩⟩ }
  exact hc.map f e.surjective

/-!
## Lemmas 2.2 and 2.3: contraction and mixing

Transfer the sorted energy estimate to arbitrary labels and iterate it over connected windows.
-/

/-- Lemma 2.2: first-crossing energy loss and the discrete Poincare estimate give
the paper's contraction factor for a connected window. -/
theorem connected_window_energy (G : SimpleGraph V) (hn : 2 ≤ Fintype.card V)
    (σ : Strategy V) (hσ : IsLegal G σ) (hc : (supportGraph G σ).Connected) (w : State V) :
    centeredEnergy (run σ w) ≤
      (1 - 4 / (Fintype.card V : ℝ) ^ 2) * centeredEnergy w := by
  classical
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : Fintype.card V ≠ 0)
  let e0 : V ≃ Fin (m + 1) := (Fintype.equivFin V).trans (finCongr hm)
  let p := Tuple.sort (w ∘ e0.symm)
  let e := e0.trans p.symm
  let H := G.comap e.symm
  let iso : G ≃g H := { toEquiv := e, map_rel_iff' := by intro a b; simp [H] }
  let τ := σ.map (Finset.map e.toEmbedding)
  have hc' : (supportGraph H τ).Connected := support_connected_map iso σ hc
  have hw : Monotone (w ∘ e.symm) := Tuple.monotone_sort (w ∘ e0.symm)
  have h := sorted_window_energy m H τ hc' (w ∘ e.symm) hw
  have heq : run τ (w ∘ e.symm) = run σ w ∘ e.symm := by
    ext v
    simpa only [Equiv.apply_symm_apply, Function.comp_apply] using run_map_equiv e σ w (e.symm v)
  rw [heq, centered_energy_reindex, centered_energy_reindex] at h
  simpa only [hm] using h

/-- Lemma 2.3: a nonempty list of connected windows satisfies the exponential
maximum-entry mixing bound towards consensus. -/
theorem connected_windows_mix (G : SimpleGraph V) (hn : 3 ≤ Fintype.card V)
    (blocks : List (Strategy V)) (hne : blocks ≠ [])
    (hblocks : ∀ σ ∈ blocks, IsLegal G σ ∧ (supportGraph G σ).Connected) :
    maxEntryNorm (strategyMatrix blocks.flatten - consensusMatrix) ≤
      Real.exp (-2 * (blocks.length : ℝ) / (Fintype.card V : ℝ) ^ 2) := by
  have hnR : (3 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < Fintype.card V := by linarith
  let c : ℝ := 1 - 4 / (Fintype.card V : ℝ) ^ 2
  have hc : 0 ≤ c := by
    dsimp [c]
    have h : 4 / (Fintype.card V : ℝ) ^ 2 ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith
    linarith
  have hiter (bs : List (Strategy V))
      (hs : ∀ σ ∈ bs, IsLegal G σ ∧ (supportGraph G σ).Connected) (w : State V) :
      centeredEnergy (run bs.flatten w) ≤ c ^ bs.length * centeredEnergy w := by
    induction bs generalizing w with
    | nil => simp [run]
    | cons σ bs ih =>
      rw [List.flatten_cons, run_append]
      have hσ := hs σ (by simp)
      calc
        _ ≤ c ^ bs.length * centeredEnergy (run σ w) :=
          ih (fun τ hτ => hs τ (by simp [hτ])) _
        _ ≤ c ^ bs.length * (c * centeredEnergy w) :=
          mul_le_mul_of_nonneg_left (connected_window_energy G (by omega) σ hσ.1 hσ.2 w)
            (pow_nonneg hc _)
        _ = _ := by simp only [List.length_cons, pow_succ]; ring
  have hpoint (j : V) : centeredEnergy (pointMass j) ≤ 1 := by
    have hm : mean Finset.univ (pointMass j) = 1 / (Fintype.card V : ℝ) := by
      simp [mean, pointMass]
    have heq : centeredEnergy (pointMass j) = 1 - 1 / (Fintype.card V : ℝ) := by
      simp only [centeredEnergy, hm, energy, Pi.sub_apply, sub_sq,
        Finset.sum_add_distrib, Finset.sum_sub_distrib]
      simp [pointMass, mul_ite, ite_mul]
      field_simp
      <;> ring
    rw [heq]
    have := one_div_pos.mpr hnpos
    linarith
  have hexp : c ≤ Real.exp (-4 / (Fintype.card V : ℝ) ^ 2) := by
    have h := Real.add_one_le_exp (-4 / (Fintype.card V : ℝ) ^ 2)
    dsimp [c]
    rw [neg_div] at h ⊢
    linarith
  have henergy (j : V) : centeredEnergy (run blocks.flatten (pointMass j)) ≤
      Real.exp (-4 * (blocks.length : ℝ) / (Fintype.card V : ℝ) ^ 2) := by
    calc
      _ ≤ c ^ blocks.length * centeredEnergy (pointMass j) := hiter blocks hblocks _
      _ ≤ c ^ blocks.length := by
        simpa using mul_le_mul_of_nonneg_left (hpoint j) (pow_nonneg hc blocks.length)
      _ ≤ (Real.exp (-4 / (Fintype.card V : ℝ) ^ 2)) ^ blocks.length :=
        pow_le_pow_left₀ hc hexp blocks.length
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  unfold maxEntryNorm
  apply (pi_norm_le_iff_of_nonneg (Real.exp_pos _).le).mpr
  rintro ⟨i, j⟩
  have hm : mean Finset.univ (run blocks.flatten (pointMass j)) =
      1 / (Fintype.card V : ℝ) := by
    change mass (run blocks.flatten (pointMass j)) / (Fintype.card V : ℝ) = _
    rw [run_mass]
    simp [mass, pointMass]
  have hcoord : (run blocks.flatten (pointMass j) i - 1 / (Fintype.card V : ℝ)) ^ 2 ≤
      centeredEnergy (run blocks.flatten (pointMass j)) := by
    simp only [centeredEnergy, energy, Pi.sub_apply, hm]
    exact Finset.single_le_sum (fun v _ =>
      sq_nonneg (run blocks.flatten (pointMass j) v - 1 / (Fintype.card V : ℝ)))
      (Finset.mem_univ i)
  have heq : (Real.exp (-2 * (blocks.length : ℝ) / (Fintype.card V : ℝ) ^ 2)) ^ 2 =
      Real.exp (-4 * (blocks.length : ℝ) / (Fintype.card V : ℝ) ^ 2) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  change |run blocks.flatten (pointMass j) i - 1 / (Fintype.card V : ℝ)| ≤ _
  have hbound := hcoord.trans (henergy j)
  rw [← heq] at hbound
  nlinarith [sq_abs (run blocks.flatten (pointMass j) i - 1 / (Fintype.card V : ℝ)),
    Real.exp_pos (-2 * (blocks.length : ℝ) / (Fintype.card V : ℝ) ^ 2)]

/-!
## Preparation for the global induction: replace blocks inside strategies

Control the required mixing radius and small graphs, then show every overly long strategy is a convex combination of shorter ones.
-/

private lemma convex_sandwich (G : SimpleGraph V) (K : Set (Matrix V V ℝ))
    (hK : Convex ℝ K) (α β γ : Strategy V) (k : ℕ)
    (hβ : strategyMatrix β ∈ operatorPolytope G k)
    (hreplace : ∀ τ, IsLegal G τ → τ.length ≤ k → strategyMatrix (α ++ τ ++ γ) ∈ K) :
    strategyMatrix (α ++ β ++ γ) ∈ K := by
  let f : Matrix V V ℝ →ₗ[ℝ] Matrix V V ℝ :=
    (LinearMap.mulLeft ℝ (strategyMatrix γ)).comp (LinearMap.mulRight ℝ (strategyMatrix α))
  have hs : operatorsWithin G k ⊆ f ⁻¹' K := by
    rintro M ⟨τ, hτ, hlen, rfl⟩
    change strategyMatrix γ * (strategyMatrix τ * strategyMatrix α) ∈ K
    simpa only [strategyMatrix_append] using hreplace τ hτ hlen
  have h := convexHull_min hs (hK.linear_preimage f) hβ
  change strategyMatrix γ * (strategyMatrix β * strategyMatrix α) ∈ K at h
  simpa only [strategyMatrix_append] using h

private lemma fixed_blocks {α : Type*} (B q : ℕ) (σ : List α) (hlen : q * B ≤ σ.length) :
    ∃ blocks : List (List α), ∃ tail,
      blocks.length = q ∧ (∀ β ∈ blocks, β.length = B) ∧ σ = blocks.flatten ++ tail := by
  induction q generalizing σ with
  | zero => exact ⟨[], σ, by simp⟩
  | succ q ih =>
    rw [Nat.succ_mul] at hlen
    have hB : B ≤ σ.length := by omega
    obtain ⟨blocks, tail, hlen', hall, heq⟩ := ih (σ.drop B) (by simp; omega)
    refine ⟨σ.take B :: blocks, tail, by simp [hlen'], ?_, ?_⟩
    · intro β hβ
      rcases List.mem_cons.mp hβ with rfl | hβ
      · simpa using hB
      · exact hall β hβ
    · simp only [List.flatten_cons, List.append_assoc, ← heq, List.take_append_drop]

private lemma mixing_radius (n : ℕ) (hn : 3 ≤ n) :
    Real.exp (-2 * (windowCount n : ℝ) / (n : ℝ) ^ 2) ≤ localRadius n := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hr : 1 ≤ logCeil n := Nat.clog_pos (by decide) (by omega)
  have hrR : (1 : ℝ) ≤ logCeil n := by exact_mod_cast hr
  have hpow : (n : ℝ) ≤ (2 : ℝ) ^ logCeil n := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) n
  have hlog : Real.log (n : ℝ) ≤ logCeil n := by
    calc _ ≤ Real.log ((2 : ℝ) ^ logCeil n) := Real.log_le_log hn0 hpow
         _ = (logCeil n : ℝ) * Real.log 2 := Real.log_pow _ _
         _ ≤ (logCeil n : ℝ) * 1 := mul_le_mul_of_nonneg_left
           (by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]) (by positivity)
         _ = _ := mul_one _
  have hlog4 : Real.log (4 : ℝ) ≤ 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num at h
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlogbound : Real.log (4 * (n : ℝ) ^ 5) ≤ 8 * logCeil n := by
    rw [Real.log_mul (by norm_num) (pow_ne_zero _ hn0.ne'), Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith
  have hrecip : Real.exp (-8 * (logCeil n : ℝ)) ≤ 1 / (4 * (n : ℝ) ^ 5) := by
    rw [neg_mul]
    rw [Real.exp_neg, one_div, inv_le_inv₀ (Real.exp_pos _) (by positivity)]
    exact Real.le_exp_of_log_le hlogbound
  have hexp : -2 * (windowCount n : ℝ) / (n : ℝ) ^ 2 = -8 * (logCeil n : ℝ) := by
    simp only [windowCount, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    field_simp
    <;> ring
  simpa only [hexp, localRadius] using hrecip

private lemma small_graph_strategy (G : SimpleGraph V) (hn : Fintype.card V ≤ 2)
    (σ : Strategy V) (hσ : IsLegal G σ) :
    strategyMatrix σ ∈ operatorPolytope G (uniformLength (Fintype.card V)) := by
  have hconst (τ : Strategy V) (c : ℝ) : run τ (fun _ => c) = fun _ => c := by
    induction τ with
    | nil => rfl
    | cons S τ ih => rw [run_cons, average_const, ih]
  induction σ with
  | nil => exact strategyMatrix_mem_polytope G [] (by simp [IsLegal]) (by simp)
  | cons S σ ih =>
    have hS := hσ S (by simp)
    have htail : IsLegal G σ := fun T hT => hσ T (by simp [hT])
    by_cases hs : S.card ≤ 1
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp (show S.card = 1 by have := hS.1.card_pos; omega)
      have heq : strategyMatrix ({v} :: σ) = strategyMatrix σ := by
        ext i j
        simp [strategyMatrix, run_cons]
      rw [heq]
      exact ih htail
    · have hScard : S.card = Fintype.card V := by have := S.card_le_univ; omega
      have hfull : S = Finset.univ := Finset.eq_univ_of_card S hScard
      have hcard : Fintype.card V = 2 := by omega
      have heq : strategyMatrix (S :: σ) = strategyMatrix [S] := by
        subst S
        ext i j
        simp only [strategyMatrix, run_cons, run_nil]
        have hc : average Finset.univ (pointMass j) = fun _ => mean Finset.univ (pointMass j) := by
          ext v; simp [average]
        rw [hc, hconst]
      rw [heq, hcard]
      exact strategyMatrix_mem_polytope G [S] (by simpa [IsLegal] using hS) (by simp [uniformLength])

private lemma uniform_recurrence (n : ℕ) (hn : 3 ≤ n) :
    uniformLength n = 2 * windowCount n * (uniformLength (n - 1) + 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  simp [Nat.add_comm, Nat.add_left_comm, uniformLength]

private lemma uniform_doubles (n : ℕ) (hn : 2 ≤ n) :
    2 * uniformLength (n - 1) ≤ uniformLength n := by
  by_cases h : n = 2
  · subst n; decide
  have h3 : 3 ≤ n := by omega
  have hr : 1 ≤ logCeil n := Nat.clog_pos (by decide) (by omega)
  have hq : 1 ≤ windowCount n := by
    change 0 < windowCount n
    unfold windowCount
    have : 0 < n := by omega
    positivity
  rw [uniform_recurrence n h3]
  nlinarith

/-- Insert local convex decompositions into the full strategy using linear maps.
Each replacement is strictly shorter. Use either a disconnected window or
local replacement after two sufficiently mixed blocks. -/
private lemma shorten_long_strategy (G : SimpleGraph V) (hn : 3 ≤ Fintype.card V)
    (hsmall : ∀ j, j < Fintype.card V → ∀ H : SimpleGraph (Fin j),
      ∀ τ : Strategy (Fin j), IsLegal H τ →
        strategyMatrix τ ∈ operatorPolytope H (uniformLength j))
    (σ : Strategy V) (hσ : IsLegal G σ)
    (hlong : uniformLength (Fintype.card V) < σ.length)
    (ih : ∀ τ, IsLegal G τ → τ.length < σ.length →
      strategyMatrix τ ∈ operatorPolytope G (uniformLength (Fintype.card V))) :
    strategyMatrix σ ∈ operatorPolytope G (uniformLength (Fintype.card V)) := by
  classical
  let n := Fintype.card V
  let B := uniformLength (n - 1) + 1
  let q := windowCount n
  change uniformLength n < σ.length at hlong
  have hL : uniformLength n = 2 * q * B := uniform_recurrence n hn
  have hr : 1 ≤ logCeil n := Nat.clog_pos (by decide) (by omega)
  have hq : 4 ≤ q := by
    have hn2 : 1 ≤ n ^ 2 := by
      change 0 < n ^ 2
      have : 0 < n := by omega
      positivity
    dsimp [q, windowCount]
    nlinarith
  have hB : 1 ≤ B := by dsimp [B]; omega
  by_cases hbad : ∃ α β γ : Strategy V, σ = α ++ β ++ γ ∧ β.length = B ∧
      ¬ (supportGraph G β).Connected
  · obtain ⟨α, β, γ, heq, hβlen, hβdisc⟩ := hbad
    have hlegal := hσ
    rw [heq, isLegal_append, isLegal_append] at hlegal
    have hshort := disconnected_window_shortening G hn uniformLength (by rfl)
      (fun j hj _ => uniform_doubles j hj) hsmall β hlegal.1.2 hβdisc
    rw [heq]
    apply convex_sandwich G _ (convex_convexHull ℝ _) α β γ
      (uniformLength (n - 1)) hshort
    intro τ hτ hlen
    apply ih _ ((isLegal_append _ _ _).mpr ⟨(isLegal_append _ _ _).mpr ⟨hlegal.1.1, hτ⟩, hlegal.2⟩)
    have hlenσ : σ.length = α.length + B + γ.length := by simp [heq, hβlen, Nat.add_assoc]
    simp only [List.length_append]
    dsimp [B] at hlenσ
    omega
  · have hgood (α β γ : Strategy V) (heq : σ = α ++ β ++ γ) (hlen : β.length = B) :
        (supportGraph G β).Connected := by
      by_contra h
      exact hbad ⟨α, β, γ, heq, hlen, h⟩
    obtain ⟨blocks, tail, hlen, hlengths, heq⟩ := fixed_blocks B (2 * q) σ (by omega)
    have hlegalblocks : ∀ β ∈ blocks, IsLegal G β := by
      intro β hβ S hS
      apply hσ S
      rw [heq]
      exact List.mem_append_left _ (List.mem_flatten.mpr ⟨β, hβ, hS⟩)
    have hconnblocks : ∀ β ∈ blocks, (supportGraph G β).Connected := by
      intro β hβ
      obtain ⟨before, after, hb⟩ := List.eq_append_cons_of_mem hβ
      apply hgood before.flatten β (after.flatten ++ tail) _ (hlengths β hβ)
      simp [heq, hb, List.append_assoc]
    let left := blocks.take q
    let right := blocks.drop q
    have hleft : left.length = q := by simp [left, hlen]; omega
    have hright : right.length = q := by simp [right, hlen]; omega
    have hleftGood : ∀ β ∈ left, IsLegal G β ∧ (supportGraph G β).Connected := by
      intro β hβ
      have h := List.mem_of_mem_take hβ
      exact ⟨hlegalblocks β h, hconnblocks β h⟩
    have hrightGood : ∀ β ∈ right, IsLegal G β ∧ (supportGraph G β).Connected := by
      intro β hβ
      have h := List.mem_of_mem_drop hβ
      exact ⟨hlegalblocks β h, hconnblocks β h⟩
    have hleftLegal : IsLegal G left.flatten := by
      intro S hS
      obtain ⟨β, hβ, hS⟩ := List.mem_flatten.mp hS
      exact (hleftGood β hβ).1 S hS
    have hrightLegal : IsLegal G right.flatten := by
      intro S hS
      obtain ⟨β, hβ, hS⟩ := List.mem_flatten.mp hS
      exact (hrightGood β hβ).1 S hS
    have hleftNonempty : left ≠ [] := by intro h; simp [h] at hleft; omega
    have hrightNonempty : right ≠ [] := by intro h; simp [h] at hright; omega
    have hG : G.Connected := by
      obtain ⟨β, hβ⟩ := List.exists_mem_of_ne_nil left hleftNonempty
      exact SimpleGraph.Connected.mono
        (show supportGraph G β ≤ G from fun _ _ h => h.1) (hleftGood β hβ).2
    have hnearL : maxEntryNorm (strategyMatrix left.flatten - consensusMatrix) ≤ localRadius n := by
      have h := connected_windows_mix G hn left hleftNonempty hleftGood
      rw [hleft] at h
      exact h.trans (mixing_radius n hn)
    have hnearR : maxEntryNorm (strategyMatrix right.flatten - consensusMatrix) ≤ localRadius n := by
      have h := connected_windows_mix G hn right hrightNonempty hrightGood
      rw [hright] at h
      exact h.trans (mixing_radius n hn)
    have hlocal := (local_replacement G hG hn _ _
      ⟨left.flatten, hleftLegal, rfl⟩ ⟨right.flatten, hrightLegal, rfl⟩ hnearL hnearR).1
    have hflatten : left.flatten ++ right.flatten = blocks.flatten := by
      rw [← List.flatten_append, List.take_append_drop]
    have hblocklen : blocks.flatten.length = 2 * q * B := by
      rw [List.length_flatten]
      have he : blocks.map List.length = List.replicate blocks.length B := by
        apply List.eq_replicate_iff.mpr
        refine ⟨by simp, ?_⟩
        intro a ha
        obtain ⟨β, hβ, rfl⟩ := List.mem_map.mp ha
        exact hlengths β hβ
      rw [he, List.sum_replicate, hlen]
      simp [smul_eq_mul]
    have hprefix : strategyMatrix blocks.flatten ∈ operatorPolytope G 6 := by
      rw [← hflatten, strategyMatrix_append]
      exact hlocal
    have htailLegal : IsLegal G tail := by
      rw [heq, isLegal_append] at hσ
      exact hσ.2
    have hσlen : σ.length = 2 * q * B + tail.length := by simp [heq, hblocklen]
    have hfull : σ = [] ++ blocks.flatten ++ tail := by simpa using heq
    rw [hfull]
    apply convex_sandwich G _ (convex_convexHull ℝ _) [] blocks.flatten tail 6 hprefix
    intro τ hτ hτlen
    apply ih _ (by simpa only [List.nil_append, isLegal_append] using And.intro hτ htailLegal)
    simp only [List.nil_append, List.length_append]
    nlinarith

/-!
## Theorem 1.1: exact convex-hull stabilization

Close the two inductions using the explicitly defined uniformLength.
-/

/-- Theorem 1.1: induction on vertex count and strategy length proves exact
stabilization of the ordinary convex hull at the explicit horizon L_n. -/
theorem uniform_convex_stabilization (G : SimpleGraph V) :
    operatorHull G = operatorPolytope G (uniformLength (Fintype.card V)) := by
  classical
  have hfin (n : ℕ) : ∀ H : SimpleGraph (Fin n), ∀ σ : Strategy (Fin n), IsLegal H σ →
      strategyMatrix σ ∈ operatorPolytope H (uniformLength n) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro H σ hσ
      by_cases hn : n ≤ 2
      · simpa only [Fintype.card_fin] using small_graph_strategy H (by simpa using hn) σ hσ
      have hn3 : 3 ≤ Fintype.card (Fin n) := by simp; omega
      have hsmall : ∀ j, j < Fintype.card (Fin n) → ∀ K : SimpleGraph (Fin j),
          ∀ τ : Strategy (Fin j), IsLegal K τ → strategyMatrix τ ∈ operatorPolytope K (uniformLength j) := by
        intro j hj K τ hτ
        exact ih j (by simpa using hj) K τ hτ
      have hlen (k : ℕ) : ∀ τ : Strategy (Fin n), IsLegal H τ → τ.length = k →
          strategyMatrix τ ∈ operatorPolytope H (uniformLength n) := by
        induction k using Nat.strong_induction_on with
        | h k hk =>
          intro τ hτ hτlen
          by_cases hshort : k ≤ uniformLength n
          · exact strategyMatrix_mem_polytope H τ hτ (by omega)
          have hlong : uniformLength (Fintype.card (Fin n)) < τ.length := by simp; omega
          simpa only [Fintype.card_fin] using shorten_long_strategy H hn3 hsmall τ hτ hlong
            (fun ρ hρ hρlen => by
              simpa only [Fintype.card_fin] using hk ρ.length (by omega) ρ hρ rfl)
      exact hlen σ.length σ hσ rfl
  have hsub : strategyOperators G ⊆ operatorPolytope G (uniformLength (Fintype.card V)) := by
    rintro M ⟨σ, hσ, rfl⟩
    exact smaller_graph_bound G _ (hfin (Fintype.card V)) σ hσ
  exact Set.Subset.antisymm (convexHull_min hsub (convex_convexHull ℝ _))
    (operatorPolytope_subset_hull G _)

/-!
## Quantitative consequences: explicit and asymptotic bounds

Estimate the recurrence by the paper's factorial bound and its quantified asymptotic form.
-/

private theorem uniformLength_positive (n : ℕ) (hn : 2 ≤ n) : 1 ≤ uniformLength n := by
  rcases n with _ | _ | _ | n
  · omega
  · omega
  · decide
  · have hlog : 0 < logCeil (n + 3) := Nat.clog_pos (by decide) (by omega)
    change 0 < 2 * windowCount (n + 3) * (uniformLength (n + 2) + 1)
    unfold windowCount
    positivity

private theorem uniformLength_step (n : ℕ) (hn : 2 ≤ n) :
    uniformLength (n + 1) ≤ 16 * (n + 1) ^ 2 * logCeil (n + 1) * uniformLength n := by
  have hp := uniformLength_positive n hn
  have heq : uniformLength (n + 1) =
      2 * windowCount (n + 1) * (uniformLength n + 1) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (show uniformLength (k + 3) = 2 * windowCount (k + 3) *
        (uniformLength (k + 2) + 1) from rfl)
  rw [heq, windowCount]
  nlinarith [Nat.mul_le_mul_left (8 * (n + 1) ^ 2 * logCeil (n + 1))
    (show uniformLength n + 1 ≤ 2 * uniformLength n by omega)]

/-- Theorem 1.1, numerical estimate: the recurrence is bounded by the stated factorial expression. -/
theorem uniformLength_le_explicitBound (n : ℕ) (hn : 2 ≤ n) :
    uniformLength n ≤ explicitBound n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [uniformLength, explicitBound]
  | succ n hn ih =>
    have hlog : logCeil n ≤ logCeil (n + 1) := Nat.clog_mono_right 2 (by omega)
    have hfac : (n + 1).factorial / 2 = (n + 1) * (n.factorial / 2) := by
      rw [Nat.factorial_succ, Nat.mul_div_assoc _ (Nat.dvd_factorial (by decide) hn)]
    have he : n + 1 - 2 = (n - 2) + 1 := by omega
    have hb : explicitBound (n + 1) =
        16 * (n + 1) ^ 2 * logCeil (n + 1) *
          (16 ^ (n - 2) * (n.factorial / 2) ^ 2 * logCeil (n + 1) ^ (n - 2)) := by
      unfold explicitBound
      rw [hfac, he, pow_succ, pow_succ]
      ring
    calc
      uniformLength (n + 1) ≤
          16 * (n + 1) ^ 2 * logCeil (n + 1) * uniformLength n := uniformLength_step n hn
      _ ≤ 16 * (n + 1) ^ 2 * logCeil (n + 1) * explicitBound n := Nat.mul_le_mul_left _ ih
      _ ≤ explicitBound (n + 1) := by
        rw [hb]
        unfold explicitBound
        gcongr

private theorem uniformLength_le_power (n : ℕ) (hn : 2 ≤ n) :
    uniformLength n ≤ (16 * n ^ 2 * logCeil n) ^ n := by
  have hl : 1 ≤ logCeil n := Nat.clog_pos (by decide) (by omega)
  have h16 : 16 ^ (n - 2) ≤ 16 ^ n := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  have hlog : logCeil n ^ (n - 2) ≤ logCeil n ^ n :=
    Nat.pow_le_pow_right hl (Nat.sub_le _ _)
  have hfac : n.factorial / 2 ≤ n ^ n := (Nat.div_le_self _ _).trans n.factorial_le_pow
  calc
    uniformLength n ≤ explicitBound n := uniformLength_le_explicitBound n hn
    _ ≤ 16 ^ n * (n ^ n) ^ 2 * logCeil n ^ n := by
      unfold explicitBound
      gcongr
    _ = (16 * n ^ 2 * logCeil n) ^ n := by
      simp only [mul_pow, ← pow_mul, Nat.mul_comm]

/-- The quantified form of n^((2+o(1))*n): for every positive epsilon, the bound is
eventually at most n^((2+epsilon)*n). -/
theorem uniformLength_asymptotic :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (uniformLength n : ℝ) ≤ (n : ℝ) ^ ((2 + ε) * (n : ℝ)) := by
  intro ε hε
  have hsmall := ((isLittleO_log_rpow_atTop hε).const_mul_left
    (32 / Real.log 2)).eventuallyLE
  have hnat : ∀ᶠ n : ℕ in Filter.atTop,
      ‖(32 / Real.log 2) * Real.log (n : ℝ)‖ ≤ ‖(n : ℝ) ^ ε‖ :=
    (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ => (n : ℝ))
      Filter.atTop Filter.atTop).eventually hsmall
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hnat
  refine ⟨max 2 N, fun n hn => ?_⟩
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hnN : N ≤ n := (le_max_right _ _).trans hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnR2 : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hlog : 1 ≤ Real.logb 2 (n : ℝ) := by
    have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2) hnR2
    simpa using h
  have hceil : (logCeil n : ℝ) ≤ Real.logb 2 (n : ℝ) + 1 := by
    rw [logCeil, ← Real.natCeil_logb_natCast]
    norm_num only [Nat.cast_ofNat]
    exact (Nat.ceil_lt_add_one (by linarith : 0 ≤ Real.logb 2 (n : ℝ))).le
  have hlim : (32 / Real.log 2) * Real.log (n : ℝ) ≤ (n : ℝ) ^ ε := by
    have h := hN n hnN
    have h' : |(32 / Real.log 2) * Real.log (n : ℝ)| ≤ (n : ℝ) ^ ε := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hnR.le _)] using h
    exact (le_abs_self _).trans h'
  have hcoeff : 16 * (logCeil n : ℝ) ≤ (n : ℝ) ^ ε := by
    have heq : (32 / Real.log 2) * Real.log (n : ℝ) = 32 * Real.logb 2 (n : ℝ) := by
      unfold Real.logb; ring
    rw [heq] at hlim
    linarith
  have hbase : (16 * n ^ 2 * logCeil n : ℝ) ≤ (n : ℝ) ^ (2 + ε) := by
    rw [Real.rpow_add hnR, Real.rpow_two]
    nlinarith [mul_le_mul_of_nonneg_left hcoeff (sq_nonneg (n : ℝ))]
  calc
    (uniformLength n : ℝ) ≤ (16 * (n : ℝ) ^ 2 * logCeil n) ^ n := by
      exact_mod_cast uniformLength_le_power n hn2
    _ ≤ ((n : ℝ) ^ (2 + ε)) ^ n := pow_le_pow_left₀ (by positivity) hbase n
    _ = (n : ℝ) ^ ((2 + ε) * (n : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnR.le]

/-!
## Structural consequence: a rational polytope

The stabilized finite horizon consists of finitely many rational strategy matrices.
-/

/-- Theorem 1.1, polytope conclusion: the full operator hull is generated by finitely many rational matrices. -/
theorem operatorHull_rationalPolytope (G : SimpleGraph V) :
    IsRationalPolytope (operatorHull G) := by
  classical
  let k := uniformLength (Fintype.card V)
  let words : Set (Strategy V) := {σ | IsLegal G σ ∧ σ.length ≤ k}
  have hwords : words.Finite :=
    (List.finite_length_le (Finset V) k).subset fun _ h => h.2
  let mq : Strategy V → Matrix V V ℚ :=
    fun σ i j => runQ σ (fun v => if v = j then 1 else 0) i
  have hcast (σ : Strategy V) :
      (fun i j => (mq σ i j : ℝ)) = strategyMatrix σ := by
    ext i j
    have hpoint : pointMass j = fun v => ((if v = j then 1 else 0 : ℚ) : ℝ) := by
      funext v; by_cases h : v = j <;> simp [pointMass, h]
    simp only [strategyMatrix, hpoint, runQ_cast, mq]
  refine ⟨(hwords.image mq).toFinset, ?_⟩
  rw [uniform_convex_stabilization]
  apply congrArg (convexHull ℝ)
  change operatorsWithin G k = _
  rw [Set.Finite.coe_toFinset]
  ext M
  constructor
  · rintro ⟨σ, hσ, hlen, rfl⟩
    exact ⟨mq σ, ⟨σ, ⟨hσ, hlen⟩, rfl⟩, hcast σ⟩
  · rintro ⟨Q, ⟨σ, ⟨hσ, hlen⟩, rfl⟩, rfl⟩
    exact ⟨σ, hσ, hlen, (hcast σ).symm⟩

/-!
## Corollary 1.2: short optimizers for linear objectives

Maximize on the finite generating set, then specialize to a target water level and the shortest optimal length.
-/

/-- Corollary 1.2: every matrix linear objective has an optimal strategy of length
at most L_n. This common length bound is independent of the objective; the
maximizing strategy may depend on the objective. -/
theorem linear_objective_attained (G : SimpleGraph V) (C : Matrix V V ℝ) :
    ∃ σ : Strategy V, IsLegal G σ ∧ σ.length ≤ uniformLength (Fintype.card V) ∧
      ∀ τ : Strategy V, IsLegal G τ →
        (∑ i, ∑ j, C i j * strategyMatrix τ i j) ≤
        ∑ i, ∑ j, C i j * strategyMatrix σ i j := by
  classical
  let f : Matrix V V ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun M => ∑ i, ∑ j, C i j * M i j
      map_add' := by intro A B; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c A
        simp [Finset.mul_sum, mul_left_comm] }
  let k := uniformLength (Fintype.card V)
  have hne : (operatorsWithin G k).Nonempty :=
    ⟨strategyMatrix [], [], by simp [IsLegal], by simp, rfl⟩
  obtain ⟨M, hM, hmax⟩ := Set.exists_max_image (operatorsWithin G k) f
    (operatorsWithin_finite G k) hne
  obtain ⟨σ, hσ, hlen, rfl⟩ := hM
  refine ⟨σ, hσ, hlen, ?_⟩
  intro τ hτ
  have hbound : operatorPolytope G k ⊆ {M | f M ≤ f (strategyMatrix σ)} :=
    convexHull_min hmax (convex_halfSpace_le f.isLinear _)
  apply hbound
  rw [← uniform_convex_stabilization]
  exact subset_convexHull ℝ _ ⟨τ, hτ, rfl⟩

/-- Corollary 1.2 for a target vertex: some globally optimal strategy has length at most L_|V|. -/
theorem exists_short_optimal (G : SimpleGraph V) (w : State V) (hw : Nonnegative w) (x : V) :
    ∃ σ, IsOptimal G w x σ ∧ σ.length ≤ uniformLength (Fintype.card V) := by
  classical
  let C : Matrix V V ℝ := fun i j => if i = x then w j else 0
  have eval (σ : Strategy V) :
      (∑ i, ∑ j, C i j * strategyMatrix σ i j) = run σ w x := by
    simpa [C, Matrix.mulVec, dotProduct, mul_comm] using
      congrFun (strategyMatrix_mulVec σ w) x
  obtain ⟨σ, hσ, hlen, hmax⟩ := linear_objective_attained G C
  refine ⟨σ, ⟨hσ, ?_⟩, hlen⟩
  intro τ hτ
  simpa only [eval] using hmax τ hτ

/-- The uniform bound stated for Paper 1's shortest optimal length. -/
theorem optimalLength_le_uniform (G : SimpleGraph V) (w : State V) (hw : Nonnegative w) (x : V) :
    optimalLength G w hw x ≤ uniformLength (Fintype.card V) :=
  (optimalLength_le_iff G w hw x _).mpr (exists_short_optimal G w hw x)

end WaterTransport.Paper3
