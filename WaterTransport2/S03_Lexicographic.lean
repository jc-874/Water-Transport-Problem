import WaterTransport2.S02_Barriers

/-!
# Paper 2, Sections 3-5: lexicographic maximality and explicit weights

Compare long-arm coordinates from the tip to the root, with alternating signs.
The explicit nonnegative integer input is the paper's formula (5.2), evaluated
in the integers before casting to real states.

Proof route: remove ineffective suffix moves; restrict to a shorter arm;
apply the three barriers recursively; identify the resulting comparison vector
with the original reference construction (Theorem 1); bound rational coordinate
denominators; convert lexicographic separation into a reward gap (Theorem 2).
Recursive vectors and strategy constructions are private proof preparations.
-/

namespace WaterTransport.Paper2

private def pathVertex (m : ℕ) (i : Fin (m + 1)) : Vertex m := ⟨i.val, by omega⟩

/-!
## Definitions: alternating comparison vector and lexicographic order

Read the long arm from tip to root, alternating signs, and compare at the first differing coordinate.
-/

/-- The vector Lambda_m(q), ordered from a_m to a_0 with alternating signs. -/
noncomputable def comparisonVector (m : ℕ) (q : State (Vertex m)) : Fin (m + 1) → ℝ :=
  fun r => (-1 : ℝ) ^ r.val * q (pathVertex m r.rev)

/-- Strict lexicographic order: all earlier coordinates agree and the first differing coordinate is smaller. -/
def LexLess {n : ℕ} (u v : Fin n → ℝ) : Prop :=
  ∃ r, (∀ s, s < r → u s = v s) ∧ u r < v r

/-- Nonstrict lexicographic comparison: vector equality or `LexLess`. -/
def LexLE {n : ℕ} (u v : Fin n → ℝ) : Prop := u = v ∨ LexLess u v

/-!
## Preparation: remove ineffective suffix moves

Preserve the output while making the suffix avoid the tip, allowing restriction to a smaller spider.
-/

/-- After the last effective move at a vertex, delete later moves touching that
vertex: they are ineffective. Preserve the final state and bound the remaining length. -/
private lemma suffix_after_last {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (σ : Strategy V) (w : State V) (x : V) (i : Fin σ.length)
    (hσ : IsLegal G σ) (hi : LastEffectiveAt σ w x i) :
    ∃ τ : Strategy V, IsLegal G τ ∧ i.val + 1 + τ.length ≤ σ.length ∧
      (∀ S ∈ τ, x ∉ S) ∧ run τ (run (σ.take (i.val + 1)) w) = run σ w := by
  classical
  induction σ using List.reverseRecOn with
  | nil => exact Fin.elim0 i
  | append_singleton σ S ih =>
    obtain ⟨hlegal, hS⟩ := (isLegal_append _ _ _).mp hσ
    by_cases he : i.val = σ.length
    · refine ⟨[], by simp, by simp [he], by simp, ?_⟩
      have hlen : i.val + 1 = (σ ++ [S]).length := by simp [he]
      rw [hlen, List.take_length, run_nil]
    · have hi' : i.val < σ.length := by have hh := i.isLt; simp at hh; omega
      let j : Fin σ.length := ⟨i.val, hi'⟩
      have hget : (σ ++ [S]).get i = σ.get j := by simp [List.get_eq_getElem, j, hi']
      have htake : (σ ++ [S]).take i.val = σ.take j.val := List.take_append_of_le_length hi'.le
      have hlast : LastEffectiveAt σ w x j := by
        refine ⟨hget ▸ hi.1, ?_, ?_⟩
        · have hh := hi.2.1
          rw [hget, htake] at hh
          exact hh
        · intro k hjk hxk
          let k' : Fin (σ ++ [S]).length := ⟨k.val, by simp⟩
          have hgetk : (σ ++ [S]).get k' = σ.get k := by simp [k', List.get_eq_getElem]
          have hh := hi.2.2 k' hjk (hgetk.symm ▸ hxk)
          rw [hgetk, List.take_append_of_le_length k.isLt.le] at hh
          exact hh
      obtain ⟨τ, hτ, hlen, hxτ, hrun⟩ := ih j hlegal hlast
      have ht : (σ ++ [S]).take (i.val + 1) = σ.take (j.val + 1) :=
        List.take_append_of_le_length hi'
      by_cases hxS : x ∈ S
      · have hfix : average S (run σ w) = run σ w := by
          let k : Fin (σ ++ [S]).length := ⟨σ.length, by simp⟩
          have hgetk : (σ ++ [S]).get k = S := by simp [k, List.get_eq_getElem]
          have hh := hi.2.2 k hi' (hgetk.symm ▸ hxS)
          rw [hgetk, show k.val = σ.length from rfl, List.take_append_length] at hh
          exact not_not.mp hh
        refine ⟨τ, hτ, by simp only [List.length_append, List.length_singleton]; dsimp [j] at hlen; omega, hxτ, ?_⟩
        rw [ht, hrun, run_append, run_singleton, hfix]
      · refine ⟨τ ++ [S], (isLegal_append _ _ _).mpr ⟨hτ, hS⟩, ?_, ?_, ?_⟩
        · simp only [List.length_append, List.length_singleton]
          dsimp [j] at hlen
          omega
        · intro T hT
          rcases List.mem_append.mp hT with hT | hT
          · exact hxτ T hT
          · simpa only [List.mem_singleton.mp hT] using hxS
        · rw [ht, run_append, hrun, run_append]

private lemma run_affine {V : Type*} [Fintype V] [DecidableEq V]
    (σ : Strategy V) (w : State V) (a b : ℝ) :
    run σ (fun v => a * w v + b) = fun v => a * run σ w v + b := by
  induction σ generalizing w with
  | nil => rfl
  | cons S σ ih => rw [run_cons, average_affine, ih]; rfl

/-!
## Preparation: restrict to a shorter arm

Transport legal sets and execution through the induced embedding after deleting the tip.
-/

/-- Embed the shorter spider by deleting the long-arm tip and shifting the two leaf indices. -/
private def shrink (m : ℕ) : Vertex m ↪ Vertex (m + 1) where
  toFun v := if v.val ≤ m then ⟨v.val, by omega⟩ else ⟨v.val + 1, by omega⟩
  inj' := by
    intro u v he
    have hh := congrArg Fin.val he
    dsimp at hh
    split_ifs at hh <;> dsimp at hh <;> apply Fin.ext <;> omega

private lemma shrink_val (m : ℕ) (v : Vertex m) :
    (shrink m v).val = if v.val ≤ m then v.val else v.val + 1 := by
  dsimp [shrink]
  split_ifs <;> rfl

private lemma shrink_B (m : ℕ) : shrink m (leafB m) = leafB (m + 1) := by
  apply Fin.ext
  simp [shrink_val, leafB]

private lemma shrink_C (m : ℕ) : shrink m (leafC m) = leafC (m + 1) := by
  apply Fin.ext
  simp [shrink_val, leafC]

private lemma shrink_adj (m : ℕ) (u v : Vertex m) :
    (spider (m + 1)).Adj (shrink m u) (shrink m v) ↔ (spider m).Adj u v := by
  simp only [spider, SimpleGraph.fromRel_adj, root, ne_eq, Fin.ext_iff, shrink_val]
  norm_num only [Fin.val_zero]
  split_ifs <;> (try simp only [false_and, or_false]) <;> omega

private lemma shrink_range (m : ℕ) (v : Vertex (m + 1)) :
    (∃ u, shrink m u = v) ↔ v ≠ tip (m + 1) := by
  constructor
  · rintro ⟨u, rfl⟩ he
    have hh := congrArg Fin.val he
    simp only [shrink_val, tip] at hh
    split_ifs at hh <;> omega
  · intro hv
    have hnv : v.val ≠ m + 1 := fun h => hv (Fin.ext h)
    by_cases hvm : v.val ≤ m
    · refine ⟨⟨v.val, by omega⟩, Fin.ext ?_⟩
      simp [shrink_val, hvm]
    · refine ⟨⟨v.val - 1, by have hh := v.isLt; omega⟩, Fin.ext ?_⟩
      rw [shrink_val, if_neg (by dsimp; omega)]
      dsimp
      omega

private def pullSet {U V : Type*} [Fintype U] [DecidableEq V]
    (e : U ↪ V) (S : Finset V) : Finset U := Finset.univ.filter fun v => e v ∈ S

private lemma map_pullSet {U V : Type*} [Fintype U] [DecidableEq V]
    (e : U ↪ V) (S : Finset V) (hS : ∀ v ∈ S, ∃ u, e u = v) :
    (pullSet e S).map e = S := by
  ext v
  simp only [Finset.mem_map, pullSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨u, hu, rfl⟩; exact hu
  · intro hv
    obtain ⟨u, rfl⟩ := hS v hv
    exact ⟨u, hv, rfl⟩

private lemma legal_embed_iff {U V : Type*} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
    (G : SimpleGraph U) (H : SimpleGraph V) (e : U ↪ V)
    (he : ∀ u v, H.Adj (e u) (e v) ↔ G.Adj u v) (T : Finset U) :
    IsLegalMove H (T.map e) ↔ IsLegalMove G T := by
  let f : ↥(T : Set U) → ↥(T.map e : Set V) := fun u => ⟨e u.val, Finset.mem_map.mpr ⟨u.val, u.property, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab; exact Subtype.ext (e.injective (congrArg Subtype.val hab))
    · intro v
      obtain ⟨u, hu, heq⟩ := Finset.mem_map.mp v.property
      exact ⟨⟨u, hu⟩, Subtype.ext heq⟩
  let iso : G.induce (T : Set U) ≃g H.induce (T.map e : Set V) :=
    { toEquiv := Equiv.ofBijective f hf
      map_rel_iff' := by intro a b; exact he a.val b.val }
  constructor
  · intro hT
    obtain ⟨v, hv⟩ := hT.1
    obtain ⟨u, hu, _⟩ := Finset.mem_map.mp hv
    exact ⟨⟨u, hu⟩, hT.2.map iso.symm.toHom iso.symm.surjective⟩
  · intro hT
    exact ⟨hT.1.map, hT.2.map iso.toHom iso.surjective⟩

private lemma restrict_tip (m : ℕ) (σ : Strategy (Vertex (m + 1)))
    (hσ : IsLegal (spider (m + 1)) σ) (havoid : ∀ S ∈ σ, tip (m + 1) ∉ S) :
    ∃ τ : Strategy (Vertex m), IsLegal (spider m) τ ∧ τ.length = σ.length ∧
      σ = τ.map (Finset.map (shrink m)) := by
  let τ := σ.map (pullSet (shrink m))
  have hmap (S) (hS : S ∈ σ) : (pullSet (shrink m) S).map (shrink m) = S := by
    apply map_pullSet
    intro v hv
    exact (shrink_range m v).mpr (fun h => havoid S hS (h ▸ hv))
  refine ⟨τ, ?_, by simp [τ], ?_⟩
  · intro T hT
    obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hT
    apply (legal_embed_iff (spider m) (spider (m + 1)) (shrink m) (shrink_adj m) _).mp
    rw [hmap S hS]
    exact hσ S hS
  · dsimp [τ]
    rw [List.map_map]
    conv_lhs => rw [← List.map_id σ]
    apply List.map_congr_left
    intro S hS
    exact (hmap S hS).symm

/-!
## Preparation: recursive comparison vectors

Encode the affine state on the smaller arm and prove the corresponding lexicographic comparison rules.
-/

/-- Extend a shorter comparison vector with a fixed first coordinate, representing the affine state `a - b*q`. -/
private noncomputable def extendVector {n : ℕ} (a b : ℝ) (u : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.cases a (fun r => (-1 : ℝ) ^ (r.val + 1) * a + b * u r)

private noncomputable def leafVector : (m : ℕ) → Fin (m + 1) → ℝ
  | 0 => fun _ => 1 / 2
  | m + 1 => extendVector (1 / ((m : ℝ) + 3)) (1 / ((m : ℝ) + 3)) (leafVector m)

private lemma leafVector_zero (m : ℕ) : leafVector m 0 = 1 / ((m : ℝ) + 2) := by
  cases m with
  | zero => norm_num [leafVector]
  | succ m => norm_num [leafVector, extendVector, Nat.cast_add, add_assoc]

private lemma comparison_zero (m : ℕ) (q : State (Vertex m)) :
    comparisonVector m q 0 = q (tip m) := by
  unfold comparisonVector
  simp only [Fin.val_zero, pow_zero, one_mul]
  congr 1

private lemma comparison_succ (m : ℕ) (q : State (Vertex (m + 1))) (r : Fin (m + 1)) :
    comparisonVector (m + 1) q r.succ = -comparisonVector m (q ∘ shrink m) r := by
  have hv : pathVertex (m + 1) r.succ.rev = shrink m (pathVertex m r.rev) := by
    apply Fin.ext
    simp only [pathVertex, Fin.val_rev, Fin.val_succ, shrink_val]
    rw [if_pos (by omega)]
    omega
  simp only [comparisonVector, Fin.val_succ, pow_succ, Function.comp_apply]
  rw [hv]
  ring

private lemma comparison_affine (m : ℕ) (q : State (Vertex m)) (a b : ℝ) (r : Fin (m + 1)) :
    comparisonVector m (fun v => a * q v + b) r =
      a * comparisonVector m q r + (-1 : ℝ) ^ r.val * b := by
  unfold comparisonVector
  ring

/-- Recover a comparison vector from the affine state on a shortened arm.
This common identity is used for all three source configurations. -/
private lemma comparison_extend (m : ℕ) (w : State (Vertex (m + 1)))
    (q : State (Vertex m)) (a b : ℝ) (htip : w (tip (m + 1)) = a)
    (hrest : w ∘ shrink m = fun v => -b * q v + a) :
    comparisonVector (m + 1) w = extendVector a b (comparisonVector m q) := by
  funext r
  refine Fin.cases ?_ (fun s => ?_) r
  · rw [comparison_zero, htip]; rfl
  · rw [comparison_succ, hrest, comparison_affine]
    simp only [extendVector, Fin.cases_succ, pow_succ]
    ring

private lemma lex_head_lt {n : ℕ} (u v : Fin (n + 1) → ℝ) (h : u 0 < v 0) : LexLess u v := by
  refine ⟨0, ?_, h⟩
  intro s hs
  exact (Fin.not_lt_zero s hs).elim

private lemma lex_extend {n : ℕ} (a b : ℝ) (hb : 0 < b) (u v : Fin n → ℝ)
    (h : LexLE u v) : LexLE (extendVector a b u) (extendVector a b v) := by
  rcases h with rfl | ⟨r, hfirst, hr⟩
  · exact Or.inl rfl
  · right
    refine ⟨r.succ, ?_, ?_⟩
    · intro s hs
      refine Fin.cases ?_ (fun t ht => ?_) s hs
      · intro _; rfl
      · have htr : t < r := by exact Fin.succ_lt_succ_iff.mp ht
        simp [extendVector, hfirst t htr]
    · simp only [extendVector, Fin.cases_succ]
      linarith [mul_lt_mul_of_pos_left hr hb]

private lemma extend_injective {n : ℕ} (a b : ℝ) (hb : b ≠ 0) :
    Function.Injective (extendVector (n := n) a b) := by
  intro u v he
  funext r
  have hh := congrFun he r.succ
  simpa [extendVector, hb] using hh

private lemma block_shrink (m : ℕ) (x : Vertex (m + 1)) (hx : m + 1 < x.val) (a : ℝ) :
    ∃ y : Vertex m, m < y.val ∧
      (profileBlock (insert x (pathPrefix (m + 1) (m + 1))) a) ∘ shrink m =
        fun v => -a * pointMass y v + a := by
  have hchoice : x = leafB (m + 1) ∨ x = leafC (m + 1) := by
    have hh := x.isLt
    simp only [leafB, leafC, Fin.ext_iff]
    omega
  have hB (v : Vertex m) :
      shrink m v ∈ insert (leafB (m + 1)) (pathPrefix (m + 1) (m + 1)) ↔ v ≠ leafC m := by
    have hh := v.isLt
    simp only [Finset.mem_insert, pathPrefix, Finset.mem_filter, Finset.mem_univ, true_and,
      leafB, leafC, ne_eq, Fin.ext_iff, shrink_val]
    split_ifs <;> omega
  have hC (v : Vertex m) :
      shrink m v ∈ insert (leafC (m + 1)) (pathPrefix (m + 1) (m + 1)) ↔ v ≠ leafB m := by
    have hh := v.isLt
    simp only [Finset.mem_insert, pathPrefix, Finset.mem_filter, Finset.mem_univ, true_and,
      leafB, leafC, ne_eq, Fin.ext_iff, shrink_val]
    split_ifs <;> omega
  rcases hchoice with rfl | rfl
  · refine ⟨leafC m, by simp [leafC], ?_⟩
    funext v
    simp only [Function.comp_apply, profileBlock, hB, pointMass]
    split_ifs <;> simp_all
  · refine ⟨leafB m, by simp [leafB], ?_⟩
    funext v
    simp only [Function.comp_apply, profileBlock, hC, pointMass]
    split_ifs <;> simp_all

/-!
## Induction: single-leaf, double-leaf, and root sources

Apply the barrier equality cases to fix the tip, reduce the arm, and keep track of the effective steps already used.
-/

/-- Single-leaf induction: attaining the tip bound uses at least one effective step;
the remaining arm reduces to another single-leaf problem. -/
private lemma leaf_lex_bound (m : ℕ) (x : Vertex m) (hx : m < x.val)
    (σ : Strategy (Vertex m)) (hσ : IsLegal (spider m) σ) :
    LexLE (comparisonVector m (run σ (pointMass x))) (leafVector m) ∧
    (comparisonVector m (run σ (pointMass x)) = leafVector m → m + 1 ≤ σ.length) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    have hb := single_leaf_source_bound m x hx σ hσ
    rcases lt_or_eq_of_le hb with hlt | heq
    · have hhead : comparisonVector m (run σ (pointMass x)) 0 < leafVector m 0 := by
        rw [comparison_zero, leafVector_zero]; exact hlt
      refine ⟨Or.inr (lex_head_lt _ _ hhead), ?_⟩
      intro he
      have hh := congrFun he 0
      linarith
    obtain ⟨_, i, hi, _, hpost⟩ := single_leaf_source_eq m x hx σ hσ heq
    obtain ⟨τ, hτ, hlen, havoid, hrun⟩ := suffix_after_last (spider m) σ (pointMass x) (tip m) i hσ hi
    cases m with
    | zero =>
      have he : comparisonVector 0 (run σ (pointMass x)) = leafVector 0 := by
        funext r
        have hr : r = 0 := Fin.ext (by have hh := r.isLt; change r.val = 0; omega)
        subst r
        rw [comparison_zero, leafVector_zero, heq]
      exact ⟨Or.inl he, fun _ => by omega⟩
    | succ k =>
      obtain ⟨ρ, hρ, hρlen, hmap⟩ := restrict_tip k τ hτ havoid
      let a : ℝ := 1 / ((k : ℝ) + 3)
      have ha : 0 < a := by dsimp [a]; positivity
      have hden : (1 : ℝ) / (((k + 1 : ℕ) : ℝ) + 2) = a := by
        dsimp [a]; norm_num [Nat.cast_add, add_assoc]
      rw [hden] at hpost heq
      obtain ⟨y, hy, hblock⟩ := block_shrink k x hx a
      let q := run ρ (pointMass y)
      have hrest : (run σ (pointMass x)) ∘ shrink k = fun v => -a * q v + a := by
        funext v
        change run σ (pointMass x) (shrink k v) = _
        rw [← hrun, hpost, hmap, run_map_embedding, hblock, run_affine]
      have hvec : comparisonVector (k + 1) (run σ (pointMass x)) =
          extendVector a a (comparisonVector k q) := by
        exact comparison_extend k _ q _ _ heq hrest
      have hh := ih k (by omega) y hy ρ hρ
      change LexLE _ (extendVector a a (leafVector k)) ∧ (_ = extendVector a a (leafVector k) → _) 
      rw [hvec]
      refine ⟨lex_extend a a ha _ _ hh.1, ?_⟩
      intro he
      have he' := extend_injective a a ha.ne' he
      have hlength := hh.2 he'
      omega

private noncomputable def doubleVector : (m : ℕ) → Fin (m + 1) → ℝ
  | 0 => fun _ => doubleBarrier 0
  | m + 1 => extendVector (doubleBarrier (m + 1))
      (doubleBarrier (m + 1) - 1 / ((m : ℝ) + 3)) (leafVector m)

private lemma doubleVector_zero (m : ℕ) : doubleVector m 0 = doubleBarrier m := by
  cases m <;> rfl

private lemma effectiveCount_le {V : Type*} [Fintype V] [DecidableEq V]
    (σ : Strategy V) (w : State V) : effectiveCount σ w ≤ σ.length := by
  classical
  exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)

private lemma double_block_shrink (m : ℕ) (b c : Vertex (m + 1))
    (hbc : (b = leafB (m + 1) ∧ c = leafC (m + 1)) ∨
      (b = leafC (m + 1) ∧ c = leafB (m + 1))) (a d : ℝ) (ha : 0 < a) :
    ∃ y : Vertex m, m < y.val ∧
      (profileBlock (insert b (pathPrefix (m + 1) (m + 1))) a + d • pointMass c) ∘ shrink m =
        fun v => -(a - d) * pointMass y v + a := by
  have hb : m + 1 < b.val := by rcases hbc with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp [leafB, leafC]
  obtain ⟨y, hy, hblock⟩ := block_shrink m b hb a
  have hc : shrink m y = c := by
    have hz := congrFun hblock y
    simp [pointMass] at hz
    have hout : shrink m y ∉ insert b (pathPrefix (m + 1) (m + 1)) := by
      intro hh
      simp only [profileBlock, if_pos hh] at hz
      exact ha.ne' hz
    have hne : shrink m y ≠ b := fun hh => hout (Finset.mem_insert.mpr (Or.inl hh))
    have hleaf : m + 1 < (shrink m y).val := by rw [shrink_val, if_neg (by omega)]; omega
    have hh := (shrink m y).isLt
    rcases hbc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals simp only [leafB, leafC, ne_eq, Fin.ext_iff] at hne ⊢
    all_goals omega
  refine ⟨y, hy, ?_⟩
  funext v
  change profileBlock _ a (shrink m v) + d * pointMass c (shrink m v) = _
  have hpoint : pointMass c (shrink m v) = pointMass y v := by
    rw [← hc]
    simp [pointMass, (shrink m).injective.eq_iff]
  rw [hpoint, show profileBlock _ a (shrink m v) = -a * pointMass y v + a from congrFun hblock v]
  ring

/-- Double-leaf induction: equality at the tip uses at least two effective steps,
after which the comparison reduces to the single-leaf case. -/
private lemma double_lex_bound (m : ℕ) (σ : Strategy (Vertex m)) (hσ : IsLegal (spider m) σ) :
    LexLE (comparisonVector m (run σ (twoLeafSource m))) (doubleVector m) ∧
    (comparisonVector m (run σ (twoLeafSource m)) = doubleVector m → m + 2 ≤ σ.length) := by
  have hb := double_leaf_barrier m σ hσ
  rcases lt_or_eq_of_le hb with hlt | heq
  · have hhead : comparisonVector m (run σ (twoLeafSource m)) 0 < doubleVector m 0 := by
      rw [comparison_zero, doubleVector_zero]; exact hlt
    refine ⟨Or.inr (lex_head_lt _ _ hhead), ?_⟩
    intro he; have hh := congrFun he 0; linarith
  obtain ⟨_, i, hi, b, c, hbc, _, hpost⟩ := double_leaf_barrier_eq m σ hσ heq
  obtain ⟨τ, hτ, hlen, havoid, hrun⟩ := suffix_after_last (spider m) σ (twoLeafSource m) (tip m) i hσ hi
  have hprefix : 2 ≤ i.val + 1 := by
    have heq' : run (σ.take (i.val + 1)) (twoLeafSource m) (tip m) = doubleBarrier m := by
      rw [hpost]
      have ht : tip m ∈ insert b (pathPrefix m m) := by simp [pathPrefix, tip]
      have htc : tip m ≠ c := by
        rcases hbc with ⟨_, rfl⟩ | ⟨_, rfl⟩
        all_goals intro h; have hh := congrArg Fin.val h; dsimp [tip, leafB, leafC] at hh; omega
      simp [profileBlock, ht, pointMass, htc]
    have hp := (double_leaf_barrier_eq m _ (fun S hS => hσ S (List.mem_of_mem_take hS)) heq').1
    exact hp.trans ((effectiveCount_le _ _).trans (List.length_take_le _ _))
  cases m with
  | zero =>
    have he : comparisonVector 0 (run σ (twoLeafSource 0)) = doubleVector 0 := by
      funext r
      have hr : r = 0 := Fin.ext (by have hh := r.isLt; change r.val = 0; omega)
      subst r
      rw [comparison_zero, doubleVector_zero, heq]
    exact ⟨Or.inl he, fun _ => by omega⟩
  | succ k =>
    obtain ⟨ρ, hρ, hρlen, hmap⟩ := restrict_tip k τ hτ havoid
    let a := doubleBarrier (k + 1)
    let d : ℝ := 1 / ((k : ℝ) + 3)
    have ha : 0 < a := by dsimp [a, doubleBarrier]; positivity
    have had : 0 < a - d := by
      have hn : (0 : ℝ) < (k : ℝ) + 3 := by positivity
      have hid : a - d = ((k : ℝ) + 2) / ((k : ℝ) + 3) ^ 2 := by
        dsimp [a, d, doubleBarrier]
        push_cast
        field_simp
        ring
      rw [hid]; positivity
    have hden : (1 : ℝ) / (((k + 1 : ℕ) : ℝ) + 2) = d := by
      dsimp [d]; norm_num [Nat.cast_add, add_assoc]
    rw [hden] at hpost
    obtain ⟨y, hy, hblock⟩ := double_block_shrink k b c hbc a d ha
    let q := run ρ (pointMass y)
    have hrest : (run σ (twoLeafSource (k + 1))) ∘ shrink k = fun v => -(a - d) * q v + a := by
      funext v
      change run σ (twoLeafSource (k + 1)) (shrink k v) = _
      rw [← hrun, hpost, hmap, run_map_embedding, hblock, run_affine]
    have hvec : comparisonVector (k + 1) (run σ (twoLeafSource (k + 1))) =
        extendVector a (a - d) (comparisonVector k q) := by
      exact comparison_extend k _ q _ _ heq hrest
    have hh := leaf_lex_bound k y hy ρ hρ
    change LexLE _ (extendVector a (a - d) (leafVector k)) ∧ (_ = extendVector a (a - d) (leafVector k) → _)
    rw [hvec]
    refine ⟨lex_extend a (a - d) had _ _ hh.1, ?_⟩
    intro he
    have he' := extend_injective a (a - d) had.ne' he
    have hlength := hh.2 he'
    omega

private noncomputable def rootVector : (m : ℕ) → Fin (m + 1) → ℝ
  | 0 => fun _ => 1
  | m + 1 => extendVector (1 / ((m : ℝ) + 2)) (1 / ((m : ℝ) + 2)) (doubleVector m)

private lemma rootVector_zero (m : ℕ) : rootVector m 0 = 1 / ((m : ℝ) + 1) := by
  cases m <;> norm_num [rootVector, extendVector, Nat.cast_add, add_assoc]

private lemma root_block_shrink (m : ℕ) (a : ℝ) :
    (profileBlock (pathPrefix (m + 1) (m + 1)) a) ∘ shrink m =
      fun v => -a * twoLeafSource m v + a := by
  funext v
  have hv := v.isLt
  simp only [Function.comp_apply, profileBlock, pathPrefix, Finset.mem_filter, Finset.mem_univ,
    true_and, shrink_val, twoLeafSource, Pi.add_apply, pointMass, leafB, leafC, Fin.ext_iff]
  split_ifs <;> try omega
  all_goals ring

private lemma root_lex_bound (m : ℕ) (hm : 1 ≤ m) (σ : Strategy (Vertex m))
    (hσ : IsLegal (spider m) σ) :
    LexLE (comparisonVector m (run σ (pointMass (root m)))) (rootVector m) ∧
    (comparisonVector m (run σ (pointMass (root m))) = rootVector m → m + 2 ≤ σ.length) := by
  have hb := root_barrier m hm σ hσ
  rcases lt_or_eq_of_le hb with hlt | heq
  · have hhead : comparisonVector m (run σ (pointMass (root m))) 0 < rootVector m 0 := by
      rw [comparison_zero, rootVector_zero]; exact hlt
    refine ⟨Or.inr (lex_head_lt _ _ hhead), ?_⟩
    intro he; have hh := congrFun he 0; linarith
  obtain ⟨i, hi, _, hpost⟩ := root_barrier_eq m hm σ hσ heq
  obtain ⟨τ, hτ, hlen, havoid, hrun⟩ := suffix_after_last (spider m) σ (pointMass (root m)) (tip m) i hσ hi
  cases m with
  | zero => omega
  | succ k =>
    obtain ⟨ρ, hρ, hρlen, hmap⟩ := restrict_tip k τ hτ havoid
    let a : ℝ := 1 / ((k : ℝ) + 2)
    have ha : 0 < a := by dsimp [a]; positivity
    have hden : (1 : ℝ) / (((k + 1 : ℕ) : ℝ) + 1) = a := by
      dsimp [a]; norm_num [Nat.cast_add, add_assoc]
    rw [hden] at hpost heq
    let q := run ρ (twoLeafSource k)
    have hrest : (run σ (pointMass (root (k + 1)))) ∘ shrink k = fun v => -a * q v + a := by
      funext v
      change run σ (pointMass (root (k + 1))) (shrink k v) = _
      rw [← hrun, hpost, hmap, run_map_embedding, root_block_shrink, run_affine]
    have hvec : comparisonVector (k + 1) (run σ (pointMass (root (k + 1)))) =
        extendVector a a (comparisonVector k q) := by
      exact comparison_extend k _ q _ _ heq hrest
    have hh := double_lex_bound k ρ hρ
    change LexLE _ (extendVector a a (doubleVector k)) ∧ (_ = extendVector a a (doubleVector k) → _)
    rw [hvec]
    refine ⟨lex_extend a a ha _ _ hh.1, ?_⟩
    intro he
    have he' := extend_injective a a ha.ne' he
    have hlength := hh.2 he'
    omega

/-!
## Identify the reference construction with the recursive bound

Compute the alternating leaf construction and relate it to the original referenceStrategy list.
-/

private def chosenLeaf (m : ℕ) (b : Bool) : Vertex m := if b then leafB m else leafC m

private def zigzag (m : ℕ) (b : Bool) : Strategy (Vertex m) :=
  ((List.range (m + 1)).reverse.map fun j =>
    insert (if Even (m - j) then chosenLeaf m b else chosenLeaf m (!b)) (pathPrefix m j))

private lemma prefix_card (m j : ℕ) (hj : j ≤ m) : (pathPrefix m j).card = j + 1 := by
  have he : pathPrefix m j = Finset.Iic (⟨j, by omega⟩ : Vertex m) := by
    ext v
    simp only [pathPrefix, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic, Fin.le_iff_val_le_val]
    omega
  rw [he, Fin.card_Iic]

private lemma shrink_map_prefix (m j : ℕ) (hj : j ≤ m) :
    (pathPrefix m j).map (shrink m) = pathPrefix (m + 1) j := by
  ext v
  simp only [Finset.mem_map, pathPrefix, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [shrink_val, if_pos hu.2]
    omega
  · intro hv
    let u : Vertex m := ⟨v.val, by omega⟩
    refine ⟨u, ⟨hv.1, by dsimp [u]; omega⟩, Fin.ext ?_⟩
    rw [shrink_val, if_pos (by dsimp [u]; omega)]

private lemma shrink_chosen (m : ℕ) (b : Bool) : shrink m (chosenLeaf m b) = chosenLeaf (m + 1) b := by
  cases b
  · exact shrink_C m
  · exact shrink_B m

private lemma zigzag_step (m : ℕ) (b : Bool) :
    zigzag (m + 1) b = insert (chosenLeaf (m + 1) b) (pathPrefix (m + 1) (m + 1)) ::
      (zigzag m (!b)).map (Finset.map (shrink m)) := by
  unfold zigzag
  rw [List.range_succ, List.reverse_append]
  simp only [List.reverse_singleton, List.singleton_append, List.map_cons, Nat.sub_self,
    show Even (0 : ℕ) by decide, if_true, List.map_map]
  congr 1
  apply List.map_congr_left
  intro j hj
  have hjm : j ≤ m := by have hh := List.mem_range.mp (List.mem_reverse.mp hj); omega
  dsimp only [Function.comp_def]
  rw [Finset.map_insert, shrink_map_prefix m j hjm]
  congr 1
  have hsub : m + 1 - j = (m - j) + 1 := by omega
  simp only [hsub, Nat.even_add_one]
  by_cases he : Even (m - j)
  · simp [he, shrink_chosen]
  · simp [he, shrink_chosen]

private lemma average_pointMass {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) (x : V) (hx : x ∈ S) :
    average S (pointMass x) = profileBlock S (1 / (S.card : ℝ)) := by
  funext v
  by_cases hv : v ∈ S
  · simp [average, mean, pointMass, profileBlock, hv, hx]
  · have hvx : v ≠ x := fun h => hv (h ▸ hx)
    simp [average, pointMass, profileBlock, hv, hvx]

private lemma first_leaf_step (m : ℕ) (b : Bool) :
    average (insert (chosenLeaf m b) (pathPrefix m m)) (pointMass (chosenLeaf m b)) =
      profileBlock (insert (chosenLeaf m b) (pathPrefix m m)) (1 / ((m : ℝ) + 2)) := by
  rw [average_pointMass _ _ (Finset.mem_insert_self _ _)]
  have hout : chosenLeaf m b ∉ pathPrefix m m := by cases b <;> simp [chosenLeaf, pathPrefix, leafB, leafC]
  rw [Finset.card_insert_of_notMem hout, prefix_card m m le_rfl]
  norm_num [Nat.cast_add, add_assoc]

private lemma chosen_block_shrink (m : ℕ) (b : Bool) (a : ℝ) :
    (profileBlock (insert (chosenLeaf (m + 1) b) (pathPrefix (m + 1) (m + 1))) a) ∘ shrink m =
      fun v => -a * pointMass (chosenLeaf m (!b)) v + a := by
  funext v
  have hv := v.isLt
  cases b
  all_goals simp only [chosenLeaf, Bool.false_eq_true, if_false, Bool.not_false, Bool.not_true, if_true,
    Function.comp_apply, profileBlock, pathPrefix, Finset.mem_insert, Finset.mem_filter,
    Finset.mem_univ, true_and, shrink_val, pointMass, leafB, leafC, Fin.ext_iff]
  all_goals split_ifs <;> try omega
  all_goals ring

private lemma zigzag_value (m : ℕ) (b : Bool) :
    comparisonVector m (run (zigzag m b) (pointMass (chosenLeaf m b))) = leafVector m := by
  induction m generalizing b with
  | zero =>
    have hzig : zigzag 0 b = [insert (chosenLeaf 0 b) (pathPrefix 0 0)] := by simp [zigzag]
    rw [hzig, run_singleton, first_leaf_step]
    funext r
    have hr : r = 0 := Fin.ext (by have hh := r.isLt; change r.val = 0; omega)
    subst r
    rw [comparison_zero, leafVector_zero]
    have ht : tip 0 ∈ insert (chosenLeaf 0 b) (pathPrefix 0 0) := by simp [pathPrefix, tip]
    simp [profileBlock, ht]
  | succ m ih =>
    rw [zigzag_step, run_cons, first_leaf_step]
    let a : ℝ := 1 / ((m : ℝ) + 3)
    have hden : (1 : ℝ) / (((m + 1 : ℕ) : ℝ) + 2) = a := by
      dsimp [a]; norm_num [Nat.cast_add, add_assoc]
    rw [hden]
    funext r
    refine Fin.cases ?_ (fun s => ?_) r
    · rw [comparison_zero, run_map_outside]
      · have ht : tip (m + 1) ∈ insert (chosenLeaf (m + 1) b) (pathPrefix (m + 1) (m + 1)) := by simp [pathPrefix, tip]
        simp [profileBlock, ht, leafVector, extendVector, a]
      · exact fun h => ((shrink_range m _).mp h) rfl
    · rw [comparison_succ]
      have hrest : (run ((zigzag m (!b)).map (Finset.map (shrink m)))
          (profileBlock (insert (chosenLeaf (m + 1) b) (pathPrefix (m + 1) (m + 1))) a)) ∘ shrink m =
          fun v => -a * run (zigzag m (!b)) (pointMass (chosenLeaf m (!b))) v + a := by
        funext v
        rw [Function.comp_apply, run_map_embedding, chosen_block_shrink, run_affine]
      rw [hrest, comparison_affine, ih]
      simp only [leafVector, extendVector, Fin.cases_succ, pow_succ]
      dsimp [a]
      ring

private lemma average_two_blocks {V : Type*} [Fintype V] [DecidableEq V]
    (P : Finset V) (b c : V) (hb : b ∉ P) (hc : c ∉ P) (hbc : b ≠ c) (a d : ℝ) :
    average (insert c P) (profileBlock (insert b P) a + d • pointMass c) =
      profileBlock (insert c P) (((P.card : ℝ) * a + d) / ((P.card : ℝ) + 1)) + a • pointMass b := by
  have hcB : c ∉ insert b P := by simp [hc, hbc.symm]
  have hbC : b ∉ insert c P := by simp [hb, hbc]
  have hmean : mean (insert c P) (profileBlock (insert b P) a + d • pointMass c) =
      ((P.card : ℝ) * a + d) / ((P.card : ℝ) + 1) := by
    unfold mean
    rw [Finset.card_insert_of_notMem hc, Finset.sum_insert hc]
    have hsum : ∑ v ∈ P, (profileBlock (insert b P) a + d • pointMass c) v = (P.card : ℝ) * a := by
      calc
        _ = ∑ _v ∈ P, a := by
          apply Finset.sum_congr rfl
          intro v hv
          have hvB : v ∈ insert b P := Finset.mem_insert_of_mem hv
          have hvc : v ≠ c := fun h => hc (h ▸ hv)
          simp [profileBlock, hvB, pointMass, hvc]
        _ = _ := by simp
    rw [hsum]
    simp [profileBlock, hcB, pointMass, Nat.cast_add, add_comm]
  funext v
  by_cases hv : v ∈ insert c P
  · have hvb : v ≠ b := fun hh => hbC (hh ▸ hv)
    simp [average, hv, hmean, profileBlock, pointMass, hvb]
  · have hvP : v ∉ P := fun hh => hv (Finset.mem_insert_of_mem hh)
    have hvc : v ≠ c := fun hh => hv (Finset.mem_insert.mpr (Or.inl hh))
    simp [average, hv, profileBlock, hvP, pointMass, hvc]

private lemma average_pointMass_outside {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) (x : V) (hx : x ∉ S) : average S (pointMass x) = pointMass x := by
  funext v
  by_cases hv : v ∈ S
  · have hvx : v ≠ x := fun h => hx (h ▸ hv)
    simp [average, mean, pointMass, hx, hv, hvx]
  · simp [average, hv]

private def pairMoves (m : ℕ) : Strategy (Vertex m) :=
  [insert (leafB m) (pathPrefix m m), insert (leafC m) (pathPrefix m m)]

private lemma pairMoves_state (m : ℕ) :
    run (pairMoves m) (twoLeafSource m) =
      profileBlock (insert (leafC m) (pathPrefix m m)) (doubleBarrier m) +
        (1 / ((m : ℝ) + 2)) • pointMass (leafB m) := by
  have hB : leafB m ∉ pathPrefix m m := by simp [pathPrefix, leafB]
  have hC : leafC m ∉ pathPrefix m m := by simp [pathPrefix, leafC]
  have hBC : leafB m ≠ leafC m := by intro h; have hh := congrArg Fin.val h; dsimp [leafB, leafC] at hh; omega
  have hfirst : average (insert (leafB m) (pathPrefix m m)) (twoLeafSource m) =
      profileBlock (insert (leafB m) (pathPrefix m m)) (1 / ((m : ℝ) + 2)) + pointMass (leafC m) := by
    change averageLinear _ (pointMass (leafB m) + pointMass (leafC m)) = _
    rw [map_add]
    change average _ _ + average _ _ = _
    rw [show average (insert (leafB m) (pathPrefix m m)) (pointMass (leafB m)) =
      profileBlock (insert (leafB m) (pathPrefix m m)) (1 / ((m : ℝ) + 2)) from first_leaf_step m true]
    rw [average_pointMass_outside _ _ (by simp [hC, hBC.symm])]
  simp only [pairMoves, run_cons, run_nil, hfirst]
  rw [show pointMass (leafC m) = (1 : ℝ) • pointMass (leafC m) by simp,
    average_two_blocks _ _ _ hB hC hBC, prefix_card m m le_rfl]
  congr 2
  unfold doubleBarrier
  push_cast
  field_simp
  ring

private def pairStrategy : (m : ℕ) → Strategy (Vertex m)
  | 0 => pairMoves 0
  | m + 1 => pairMoves (m + 1) ++ (zigzag m true).map (Finset.map (shrink m))

private lemma pairStrategy_value (m : ℕ) :
    comparisonVector m (run (pairStrategy m) (twoLeafSource m)) = doubleVector m := by
  cases m with
  | zero =>
    rw [pairStrategy, pairMoves_state]
    funext r
    have hr : r = 0 := Fin.ext (by have hh := r.isLt; change r.val = 0; omega)
    subst r
    rw [comparison_zero, doubleVector_zero]
    norm_num [profileBlock, pointMass, pathPrefix, tip, leafB, leafC]
  | succ m =>
    rw [pairStrategy, run_append, pairMoves_state]
    let a := doubleBarrier (m + 1)
    let d : ℝ := 1 / ((m : ℝ) + 3)
    have hden : (1 : ℝ) / (((m + 1 : ℕ) : ℝ) + 2) = d := by dsimp [d]; norm_num [Nat.cast_add, add_assoc]
    rw [hden]
    have hrest : (profileBlock (insert (leafC (m + 1)) (pathPrefix (m + 1) (m + 1))) a +
        d • pointMass (leafB (m + 1))) ∘ shrink m = fun v => -(a - d) * pointMass (leafB m) v + a := by
      funext v
      have hb : pointMass (leafB (m + 1)) (shrink m v) = pointMass (leafB m) v := by
        rw [← shrink_B m]; simp [pointMass, (shrink m).injective.eq_iff]
      change profileBlock _ a (shrink m v) + d * pointMass (leafB (m + 1)) (shrink m v) = _
      have hbl := congrFun (chosen_block_shrink m false a) v
      change profileBlock (insert (leafC (m + 1)) (pathPrefix (m + 1) (m + 1))) a (shrink m v) =
        -a * pointMass (leafB m) v + a at hbl
      rw [hb, hbl]
      ring
    funext r
    refine Fin.cases ?_ (fun s => ?_) r
    · rw [comparison_zero, run_map_outside]
      · have ht : tip (m + 1) ∈ insert (leafC (m + 1)) (pathPrefix (m + 1) (m + 1)) := by simp [pathPrefix, tip]
        have hn : tip (m + 1) ≠ leafB (m + 1) := by intro h; have hh := congrArg Fin.val h; dsimp [tip, leafB] at hh; omega
        simp [profileBlock, ht, pointMass, hn, doubleVector, extendVector]
      · exact fun h => ((shrink_range m _).mp h) rfl
    · rw [comparison_succ]
      have he : (run ((zigzag m true).map (Finset.map (shrink m)))
          (profileBlock (insert (leafC (m + 1)) (pathPrefix (m + 1) (m + 1))) a + d • pointMass (leafB (m + 1)))) ∘ shrink m =
          fun v => -(a - d) * run (zigzag m true) (pointMass (leafB m)) v + a := by
        funext v
        rw [Function.comp_apply, run_map_embedding, hrest, run_affine]
      rw [he, comparison_affine]
      rw [show comparisonVector m (run (zigzag m true) (pointMass (leafB m))) = leafVector m from zigzag_value m true]
      simp only [doubleVector, extendVector, Fin.cases_succ, pow_succ]
      dsimp [a, d]
      ring

/-- Identify the original parity-based reference list with two initial moves and
the alternating shorter-arm construction, preserving the original definition. -/
private lemma reference_strategy_split (k : ℕ) :
    referenceStrategy (k + 2) = pathPrefix (k + 2) (k + 2) ::
      (pairStrategy (k + 1)).map (Finset.map (shrink (k + 1))) := by
  unfold referenceStrategy pairStrategy pairMoves
  simp only [List.map_cons, List.cons_append, List.nil_append]
  rw [show k + 2 - 1 = k + 1 by omega]
  simp only [Finset.map_insert, shrink_map_prefix (k + 1) (k + 1) le_rfl, shrink_B, shrink_C]
  congr 1
  unfold zigzag
  rw [List.map_map, List.map_map]
  congr 1
  congr 1
  apply List.map_congr_left
  intro j hj
  have hjk : j ≤ k := by have hh := List.mem_range.mp (List.mem_reverse.mp hj); omega
  dsimp only [Function.comp_def]
  rw [Finset.map_insert, Finset.map_insert, shrink_map_prefix k j hjk,
    shrink_map_prefix (k + 1) j (by omega)]
  congr 1
  have hsub : k + 2 - j = k - j + 2 := by omega
  simp only [hsub, show k - j + 2 = (k - j + 1) + 1 by omega, Nat.even_add_one, not_not]
  by_cases he : Even (k - j)
  · simp [he, chosenLeaf, shrink_B]
  · simp [he, chosenLeaf, shrink_C]

private lemma reference_vector (m : ℕ) (hm : 2 ≤ m) :
    comparisonVector m (referenceProfile m) = rootVector m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  unfold referenceProfile
  rw [reference_strategy_split, run_cons]
  have hroot : root (k + 2) ∈ pathPrefix (k + 2) (k + 2) := by simp [pathPrefix, root]
  rw [average_pointMass _ _ hroot, prefix_card _ _ le_rfl]
  let a : ℝ := 1 / ((k : ℝ) + 3)
  have hden : (1 : ℝ) / ((k + 2 + 1 : ℕ) : ℝ) = a := by dsimp [a]; push_cast; congr 1; ring
  rw [hden]
  funext r
  refine Fin.cases ?_ (fun s => ?_) r
  · rw [comparison_zero, run_map_outside]
    · have ht : tip (k + 2) ∈ pathPrefix (k + 2) (k + 2) := by simp [pathPrefix, tip]
      norm_num [profileBlock, ht, rootVector, extendVector, a, Nat.cast_add, add_assoc]
    · exact fun h => ((shrink_range (k + 1) _).mp h) rfl
  · rw [comparison_succ]
    have hrest : (run ((pairStrategy (k + 1)).map (Finset.map (shrink (k + 1))))
        (profileBlock (pathPrefix (k + 2) (k + 2)) a)) ∘ shrink (k + 1) =
        fun v => -a * run (pairStrategy (k + 1)) (twoLeafSource (k + 1)) v + a := by
      funext v
      rw [Function.comp_apply, run_map_embedding, root_block_shrink, run_affine]
    rw [hrest, comparison_affine, pairStrategy_value]
    simp only [rootVector, extendVector, Fin.cases_succ, pow_succ]
    dsimp [a]
    push_cast
    ring

/-!
## Theorem 1: maximality and equality-length lower bound

Expose the three public consequences of the recursive comparison argument.
-/

/-- Theorem 1, maximality: every finitely reachable profile is lexicographically
bounded by the reference profile's alternating comparison vector. -/
theorem profile_lex_maximal (m : ℕ) (hm : 2 ≤ m) (q : State (Vertex m))
    (hq : q ∈ reachableProfiles m) :
    LexLE (comparisonVector m q) (comparisonVector m (referenceProfile m)) := by
  rw [reference_vector m hm]
  obtain ⟨σ, hσ, rfl⟩ := hq
  exact (root_lex_bound m (by omega) σ hσ).1

/-- Theorem 1, equality case: matching the reference comparison vector requires at least m+2 moves. Equality of the entire profile is not required. -/
theorem profile_length_of_comparison_eq (m : ℕ) (hm : 2 ≤ m)
    (q : State (Vertex m)) (hq : q ∈ reachableProfiles m)
    (heq : comparisonVector m q = comparisonVector m (referenceProfile m)) :
    m + 2 ≤ profileLength m q hq := by
  obtain ⟨σ, hσ, hlen, hval⟩ := profileLength_spec m q hq
  have hh := (root_lex_bound m (by omega) σ hσ).2 (by rw [hval, heq, reference_vector m hm])
  rwa [hlen] at hh

/-- Theorem 1, short-horizon consequence: every profile reachable in at most m+1 moves is strictly smaller in comparison order. -/
theorem short_profile_lex_lt (m : ℕ) (hm : 2 ≤ m) (q : State (Vertex m))
    (hq : q ∈ profilesWithin m (m + 1)) :
    LexLess (comparisonVector m q) (comparisonVector m (referenceProfile m)) := by
  obtain ⟨σ, hσ, hlen, hval⟩ := hq
  have hr : q ∈ reachableProfiles m := ⟨σ, hσ, hval⟩
  rcases profile_lex_maximal m hm q hr with heq | hlt
  · have hlower := profile_length_of_comparison_eq m hm q hr heq
    have hupper := profileLength_le m q hr σ hσ hval
    omega
  · exact hlt

/-!
## Definition of the explicit integer weights

Use the paper's fixed Q and B and prove that the resulting initial state is nonnegative.
-/

/-- The explicit natural numbers Q and B from the paper, used to define separating integer weights. -/
def weightBase (m : ℕ) : ℕ := 4 * (m + 3) ^ (2 * (m + 2))
/-- The constant offset B = Q^(m-1) ensuring nonnegative initial weights in the main theorem's range. -/
def weightOffset (m : ℕ) : ℕ := weightBase m ^ (m - 1)

/-- Equation (5.2): alternating powers along the long arm, with offset B at every vertex; signs are evaluated in the integers. -/
def integerWeights (m : ℕ) (v : Vertex m) : ℤ :=
  if v.val ≤ m then
    (weightOffset m : ℤ) + (-1 : ℤ) ^ (m - v.val) * (weightBase m : ℤ) ^ v.val
  else weightOffset m

/-- The explicit integer input embedded coordinatewise into the shared real state type. -/
def weights (m : ℕ) : State (Vertex m) := fun v => (integerWeights m v : ℝ)

theorem weights_nonnegative (m : ℕ) (hm : 2 ≤ m) : Nonnegative (weights m) := by
  intro v
  change (0 : ℝ) ≤ (integerWeights m v : ℝ)
  suffices h : 0 ≤ integerWeights m v by exact_mod_cast h
  unfold integerWeights
  split_ifs with hv
  · by_cases he : v.val = m
    · simp [he]; positivity
    have hi : v.val ≤ m - 1 := by omega
    have hbase : (1 : ℤ) ≤ weightBase m := by
      have hp : 0 < (m + 3) ^ (2 * (m + 2)) := pow_pos (by omega) _
      unfold weightBase
      exact_mod_cast (show 1 ≤ 4 * (m + 3) ^ (2 * (m + 2)) by omega)
    rcases neg_one_pow_eq_or ℤ (m - v.val) with h | h
    · simp only [h, one_mul]; positivity
    · simp only [h, neg_one_mul, ← sub_eq_add_neg]
      apply sub_nonneg.mpr
      change (weightBase m : ℤ) ^ v.val ≤ ((weightBase m ^ (m - 1) : ℕ) : ℤ)
      rw [Nat.cast_pow]
      exact pow_le_pow_right₀ hbase hi
  · positivity

/-!
## Preparation for strict separation: denominators and positional weights

Bound a nonzero rational coordinate gap and show the first differing coordinate dominates the weighted tail.
-/

private lemma profile_integer_denominator {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x : V)
    (σ : Strategy V) (hσ : IsLegal G σ) :
    ∃ D : ℕ, 0 < D ∧ D ≤ Fintype.card V ^ σ.length ∧
      ∃ z : V → ℤ, ∀ v, (D : ℝ) * run σ (pointMass x) v = z v := by
  classical
  induction σ using List.reverseRecOn with
  | nil =>
    refine ⟨1, by omega, by simp, fun v => if v = x then 1 else 0, ?_⟩
    intro v
    simp [run, pointMass]
  | append_singleton σ S ih =>
    have hlegal := (isLegal_append G σ [S]).mp hσ
    have hS := hlegal.2 S (by simp)
    obtain ⟨D, hD0, hD, z, hz⟩ := ih hlegal.1
    have hs0 : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.1.card_pos.ne'
    refine ⟨D * S.card, Nat.mul_pos hD0 hS.1.card_pos, ?_,
      fun v => if v ∈ S then ∑ u ∈ S, z u else (S.card : ℤ) * z v, ?_⟩
    · simp only [List.length_append, List.length_singleton, pow_succ]
      exact Nat.mul_le_mul hD S.card_le_univ
    · intro v
      rw [run_append]
      change (D * S.card : ℕ) * average S (run σ (pointMass x)) v = _
      by_cases hv : v ∈ S
      · simp only [if_pos hv, Int.cast_sum, average_apply_mem S _ hv, Nat.cast_mul]
        calc
          _ = (D : ℝ) * ∑ u ∈ S, run σ (pointMass x) u := by unfold mean; field_simp
          _ = _ := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun u _ => hz u)
      · simp only [if_neg hv, Int.cast_mul, Int.cast_natCast, average_apply_not_mem S _ hv, Nat.cast_mul]
        calc _ = (S.card : ℝ) * ((D : ℝ) * run σ (pointMass x) v) := by ring
             _ = _ := by rw [hz]

private lemma profile_probability {V : Type*} [Fintype V] [DecidableEq V]
    (x : V) (σ : Strategy V) :
    mass (run σ (pointMass x)) = 1 ∧ ∀ v, 0 ≤ run σ (pointMass x) v ∧ run σ (pointMass x) v ≤ 1 := by
  have hnonneg : Nonnegative (run σ (pointMass x)) :=
    run_nonnegative σ (fun v => by simp only [pointMass]; split_ifs <;> norm_num)
  have hm : mass (run σ (pointMass x)) = 1 := by rw [run_mass]; simp [mass, pointMass]
  refine ⟨hm, fun v => ⟨hnonneg v, ?_⟩⟩
  calc _ ≤ ∑ u, run σ (pointMass x) u := Finset.single_le_sum (fun u _ => hnonneg u) (Finset.mem_univ v)
       _ = 1 := hm

/-- The difference of two finite averaging profiles has a common integer denominator
bounded by the product of their strategy denominators. -/
private lemma profile_difference_gap (m : ℕ) (hm : 2 ≤ m) (q : State (Vertex m))
    (hq : q ∈ profilesWithin m (m + 1)) :
    ∃ D : ℕ, 0 < D ∧ 4 * D ≤ weightBase m ∧
      (∀ v, |referenceProfile m v - q v| ≤ 1) ∧
      ∀ v, ∃ z : ℤ, (D : ℝ) * (referenceProfile m v - q v) = z := by
  obtain ⟨σ, hσ, hlen, hval⟩ := hq
  obtain ⟨A, hA0, hA, a, ha⟩ := profile_integer_denominator (spider m) (root m)
    (referenceStrategy m) (referenceStrategy_legal m hm)
  obtain ⟨B, hB0, hB, b, hb⟩ := profile_integer_denominator (spider m) (root m) σ hσ
  rw [referenceStrategy_length m hm, Fintype.card_fin] at hA
  rw [Fintype.card_fin] at hB
  have hB' : B ≤ (m + 3) ^ (m + 1) := hB.trans (Nat.pow_le_pow_right (by omega) hlen)
  have hprod : A * B ≤ (m + 3) ^ (2 * (m + 2)) := by
    calc
      A * B ≤ (m + 3) ^ (m + 2) * (m + 3) ^ (m + 1) := Nat.mul_le_mul hA hB'
      _ = (m + 3) ^ ((m + 2) + (m + 1)) := (pow_add _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  refine ⟨A * B, Nat.mul_pos hA0 hB0, Nat.mul_le_mul_left 4 hprod, ?_, ?_⟩
  · intro v
    have hr := (profile_probability (root m) (referenceStrategy m)).2 v
    have hqv := (profile_probability (root m) σ).2 v
    rw [hval] at hqv
    exact abs_le.mpr ⟨by dsimp [referenceProfile]; linarith, by dsimp [referenceProfile]; linarith⟩
  · intro v
    refine ⟨(B : ℤ) * a v - (A : ℤ) * b v, ?_⟩
    have ha' : (A : ℝ) * referenceProfile m v = a v := ha v
    have hb' : (B : ℝ) * q v = b v := by rw [← hval]; exact hb v
    push_cast
    calc
      _ = (B : ℝ) * ((A : ℝ) * referenceProfile m v) - (A : ℝ) * ((B : ℝ) * q v) := by ring
      _ = _ := by rw [ha', hb']

private lemma geometric_tail_lt (D Q : ℝ) (hD : 0 < D) (hQ : D + 1 ≤ Q) (n : ℕ) :
    D * (∑ i : Fin n, Q ^ i.val) < Q ^ n := by
  have hQ0 : 0 < Q := by linarith
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, pow_succ]
    have hp : 0 < Q ^ n := pow_pos hQ0 _
    nlinarith [mul_le_mul_of_nonneg_right hQ hp.le]

private lemma polynomial_positive {n : ℕ} (c : Fin n → ℝ) (D Q : ℝ)
    (hD : 0 < D) (hQ : D + 1 ≤ Q) (hc : ∀ i, -D ≤ c i)
    (k : Fin n) (hk : 1 ≤ c k) (hhigh : ∀ j, k < j → c j = 0) :
    0 < ∑ j, c j * Q ^ j.val := by
  have hQ0 : 0 < Q := by linarith
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    by_cases he : k = Fin.last n
    · subst k
      have htail : -D * (∑ j : Fin n, Q ^ j.val) ≤
          ∑ j : Fin n, c j.castSucc * Q ^ j.val := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hc j.castSucc) (pow_nonneg hQ0.le _)
      have hlead := mul_le_mul_of_nonneg_right hk (pow_nonneg hQ0.le n)
      have hgeom := geometric_tail_lt D Q hD hQ n
      simp only [one_mul] at hlead
      nlinarith
    · have hkn : k.val < n := by
        have hn := k.isLt
        have hv : k.val ≠ n := by intro h; apply he; exact Fin.ext h
        omega
      let k' : Fin n := ⟨k.val, hkn⟩
      have hk' : k'.castSucc = k := Fin.ext rfl
      have hlast : c (Fin.last n) = 0 := hhigh _ (by change k.val < n; exact hkn)
      rw [hlast, zero_mul, add_zero]
      exact ih (fun j => c j.castSucc) (fun j => hc j.castSucc) k'
        (by simpa [hk'] using hk) (fun j hj => hhigh j.castSucc (by simpa [← hk'] using hj))

private lemma weighted_difference (m : ℕ) (p q : State (Vertex m)) (hmass : mass p = mass q) :
    pairing p (weights m) - pairing q (weights m) =
      ∑ j : Fin (m + 1), (-1 : ℝ) ^ (m - j.val) *
        (p (pathVertex m j) - q (pathVertex m j)) * (weightBase m : ℝ) ^ j.val := by
  classical
  let f : Vertex m → ℝ := fun v => if v.val ≤ m then
    (-1 : ℝ) ^ (m - v.val) * (p v - q v) * (weightBase m : ℝ) ^ v.val else 0
  have heach (v : Vertex m) : (p v - q v) * weights m v =
      (p v - q v) * (weightOffset m : ℝ) + f v := by
    dsimp [weights, integerWeights, f]
    split_ifs <;> push_cast <;> ring
  have hsum : pairing p (weights m) - pairing q (weights m) = ∑ v, f v := by
    unfold pairing
    rw [← Finset.sum_sub_distrib]
    simp_rw [← sub_mul, heach]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib]
    change (mass p - mass q) * _ + _ = _
    rw [hmass, sub_self, zero_mul, zero_add]
  rw [hsum, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [f, Fin.val_last, Fin.val_castSucc]
  simp only [show ¬ m + 2 ≤ m by omega, show ¬ m + 1 ≤ m by omega, if_false, add_zero]
  apply Finset.sum_congr rfl
  intro j _
  rw [if_pos (show j.val ≤ m by omega)]
  rfl

/-!
## Theorem 2: strict reward separation

Combine the short-profile lexicographic gap with the explicit integer weights.
-/

/-- Theorem 2: the explicit nonnegative integer weights strictly separate the
reference profile from every profile reachable in at most `m + 1` moves. -/
theorem short_profile_reward_lt (m : ℕ) (hm : 2 ≤ m) (q : State (Vertex m))
    (hq : q ∈ profilesWithin m (m + 1)) :
    pairing q (weights m) < pairing (referenceProfile m) (weights m) := by
  classical
  obtain ⟨D, hD, hDQ, hbound, hint⟩ := profile_difference_gap m hm q hq
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hQ : (D : ℝ) + 1 ≤ weightBase m := by exact_mod_cast (show D + 1 ≤ weightBase m by omega)
  let c : Fin (m + 1) → ℝ := fun j => (D : ℝ) * ((-1 : ℝ) ^ (m - j.val) *
    (referenceProfile m (pathVertex m j) - q (pathVertex m j)))
  obtain ⟨r, hfirst, hr⟩ := short_profile_lex_lt m hm q hq
  let k := r.rev
  have hkval : m - k.val = r.val := by
    change m - (m + 1 - (r.val + 1)) = r.val
    omega
  have hcpos : 0 < c k := by
    dsimp [c]
    rw [hkval]
    apply mul_pos hD0
    change (-1 : ℝ) ^ r.val * q (pathVertex m r.rev) <
      (-1 : ℝ) ^ r.val * referenceProfile m (pathVertex m r.rev) at hr
    dsimp [k]
    nlinarith
  have hclead : 1 ≤ c k := by
    obtain ⟨z, hz⟩ := hint (pathVertex m k)
    have hcint : c k = ((-1 : ℤ) ^ (m - k.val) * z : ℤ) := by
      push_cast
      dsimp [c]
      rw [mul_left_comm, hz]
    rw [hcint] at hcpos ⊢
    have hi : (0 : ℤ) < (-1 : ℤ) ^ (m - k.val) * z := by exact_mod_cast hcpos
    exact_mod_cast (show (1 : ℤ) ≤ (-1 : ℤ) ^ (m - k.val) * z by omega)
  have hc : ∀ j, -(D : ℝ) ≤ c j := by
    intro j
    have ha : |c j| ≤ D := by
      dsimp [c]
      rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos hD0]
      simpa using mul_le_mul_of_nonneg_left (hbound (pathVertex m j)) hD0.le
    exact (abs_le.mp ha).1
  have hhigh : ∀ j, k < j → c j = 0 := by
    intro j hj
    have hjr : j.rev < r := by
      change j.rev.val < r.val
      change k.val < j.val at hj
      dsimp [k] at hj
      simp only [Fin.val_rev] at hj ⊢
      omega
    have he := hfirst j.rev hjr
    change (-1 : ℝ) ^ j.rev.val * q (pathVertex m j.rev.rev) =
      (-1 : ℝ) ^ j.rev.val * referenceProfile m (pathVertex m j.rev.rev) at he
    simp only [Fin.rev_rev, Fin.val_rev] at he
    rw [show m + 1 - (j.val + 1) = m - j.val by omega] at he
    dsimp [c]
    have hzero : (-1 : ℝ) ^ (m - j.val) *
        (referenceProfile m (pathVertex m j) - q (pathVertex m j)) = 0 := by nlinarith [he]
    rw [hzero, mul_zero]
  have hp := polynomial_positive c (D : ℝ) (weightBase m : ℝ) hD0 hQ hc k hclead hhigh
  have hmass : mass (referenceProfile m) = mass q := by
    obtain ⟨σ, _, _, hval⟩ := hq
    rw [← hval]
    exact (profile_probability (root m) (referenceStrategy m)).1.trans
      (profile_probability (root m) σ).1.symm
  have hident : (D : ℝ) * (pairing (referenceProfile m) (weights m) - pairing q (weights m)) =
      ∑ j, c j * (weightBase m : ℝ) ^ j.val := by
    rw [weighted_difference m _ _ hmass, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [c]
    ring
  rw [← hident] at hp
  exact sub_pos.mp ((mul_pos_iff_of_pos_left hD0).mp hp)

end WaterTransport.Paper2
