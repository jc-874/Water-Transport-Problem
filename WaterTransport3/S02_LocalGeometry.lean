import WaterTransport3.S01_Operators
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Order.Interval.Finset.Fin
import WaterTransport1.S06_PathGeometry
import Mathlib.Analysis.Convex.Combination
import Mathlib.Order.WellFounded
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Paper 3, Sections 3-5: exact local convex decompositions

This file proves the local replacement theorem used by the uniform length bound.
The geometric ingredients are conclusions proved here, rather than assumptions
added to the global theorem. Total nonnegativity checks every ordered minor.

Proof route: connected cuts and non-cut vertices; spanning-tree coordinates;
signed rank-one directions and the nonpath neighborhood (Proposition 4.3);
path total nonnegativity and monotone-cone estimates; the path decompositions
(Lemma 5.1 and Proposition 5.5); the common six-step interface (Proposition 2.4).
-/

namespace WaterTransport.Paper3

variable {V : Type*} [Fintype V] [DecidableEq V]

/-!
## Definitions: cuts, two-block averages, and graph classes

Fix the vectors and predicates needed for both the path and nonpath branches.
-/

/-- The centered indicator of S: subtract its relative cardinality from each coordinate. -/
noncomputable def cutVector (S : Finset V) : State V :=
  fun v => (if v ∈ S then 1 else 0) - (S.card : ℝ) / Fintype.card V

/-- The squared Euclidean length of the centered cut indicator. -/
noncomputable def cutEnergy (S : Finset V) : ℝ := pairing (cutVector S) (cutVector S)

/-- Average S and its complement separately; these disjoint averages commute. -/
noncomputable def twoBlockMatrix (S : Finset V) : Matrix V V ℝ :=
  averagingMatrix S * averagingMatrix (Finset.univ \ S)

/-- Both sides of the cut are nonempty and induce connected subgraphs. -/
def IsConnectedCut (G : SimpleGraph V) (S : Finset V) : Prop :=
  IsLegalMove G S ∧ IsLegalMove G (Finset.univ \ S)

/-- Deleting this vertex leaves a connected induced subgraph. -/
def IsNonCut (G : SimpleGraph V) (v : V) : Prop :=
  (G.induce {u | u ≠ v}).Connected

/-- The graph is isomorphic to the path on the same number of vertices. -/
def IsPathGraph (G : SimpleGraph V) : Prop :=
  Nonempty (G ≃g SimpleGraph.pathGraph (Fintype.card V))

/-!
## Graph preparation and Lemma 4.1: non-cut vertices

Find a non-cut vertex outside a proper connected set and characterize the exceptional path case.
-/

private lemma crossing_edge (G : SimpleGraph V) (hG : G.Connected)
    (S : Finset V) (hne : S.Nonempty) (hproper : S ≠ Finset.univ) :
    ∃ u ∈ S, ∃ v ∉ S, G.Adj u v := by
  obtain ⟨u, hu⟩ := hne
  obtain ⟨v, hv⟩ : ∃ v, v ∉ S := by
    by_contra! h
    exact hproper (Finset.eq_univ_of_forall h)
  obtain ⟨p⟩ := hG u v
  have step {a b : V} (q : G.Walk a b) :
      a ∈ S → b ∉ S → ∃ x ∈ S, ∃ y ∉ S, G.Adj x y := by
    induction q with
    | nil => exact fun ha hb => (hb ha).elim
    | @cons a b c hab q ih =>
      intro ha hc
      by_cases hb : b ∈ S
      · exact ih hb hc
      · exact ⟨a, ha, b, hb, hab⟩
  exact step p hu hv

/-- A proper connected vertex set has a non-cut vertex outside it.
Extend the set to a maximal proper connected set to obtain such a vertex. -/
private lemma noncut_outside (G : SimpleGraph V) (hG : G.Connected)
    (S : Finset V) (hS : IsLegalMove G S) (hproper : S ≠ Finset.univ) :
    ∃ v ∉ S, IsNonCut G v := by
  classical
  let candidates := Finset.univ.filter fun T : Finset V =>
    S ⊆ T ∧ IsLegalMove G T ∧ T ≠ Finset.univ
  have hmem : S ∈ candidates := by simp [candidates, hS, hproper]
  obtain ⟨T, hT, hmax⟩ := candidates.exists_max_image Finset.card ⟨S, hmem⟩
  simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and] at hT
  obtain ⟨u, hu, v, hv, huv⟩ := crossing_edge G hG T hT.2.1.1 hT.2.2
  have hconn : IsLegalMove G (insert v T) := by
    refine ⟨Finset.insert_nonempty _ _, ?_⟩
    have heq : ((insert v T : Finset V) : Set V) = (T : Set V) ∪ {u, v} := by
      ext x
      simp only [Finset.mem_coe, Finset.mem_insert, Set.mem_union,
        Set.mem_insert_iff, Set.mem_singleton_iff]
      aesop
    rw [heq]
    exact SimpleGraph.induce_union_connected hT.2.1.2.preconnected
      (SimpleGraph.induce_pair_connected_of_adj huv).preconnected ⟨u, hu, by simp⟩
  have hfull : insert v T = Finset.univ := by
    by_contra h
    have hi : insert v T ∈ candidates := by
      simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hT.1.trans (Finset.subset_insert _ _), hconn, h⟩
    have := hmax _ hi
    rw [Finset.card_insert_of_notMem hv] at this
    omega
  refine ⟨v, fun h => hv (hT.1 h), ?_⟩
  have heq : (T : Set V) = {x | x ≠ v} := by
    ext x
    constructor
    · intro hx h
      exact hv (h ▸ hx)
    · intro hx
      change x ≠ v at hx
      have : x ∈ insert v T := by rw [hfull]; exact Finset.mem_univ x
      simpa [hx] using this
  unfold IsNonCut
  rw [← heq]
  exact hT.2.1.2

private lemma path_of_shortest_cover (G : SimpleGraph V) {a b : V}
    (p : G.Walk a b) (hp : p.length = G.dist a b)
    (hcover : ∀ v, v ∈ p.support) : IsPathGraph G := by
  classical
  let f : Fin (p.length + 1) → V := fun i => p.getVert i
  have hdist (i : Fin (p.length + 1)) : G.dist a (f i) = i := by
    have h := SimpleGraph.length_eq_dist_of_subwalk hp (p.isSubwalk_take i)
    simpa [f, p.take_length, Nat.min_eq_left (by omega : i.val ≤ p.length)] using h.symm
  have hinj : Function.Injective f := by
    intro i j h
    apply Fin.ext
    simpa [hdist] using congrArg (G.dist a) h
  have hsurj : Function.Surjective f := by
    intro v
    obtain ⟨i, hi, hib⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (hcover v)
    exact ⟨⟨i, by omega⟩, hi⟩
  let e : Fin (p.length + 1) ≃ V := Equiv.ofBijective f ⟨hinj, hsurj⟩
  have hrel (i j : Fin (p.length + 1)) :
      G.Adj (f i) (f j) ↔ (SimpleGraph.pathGraph (p.length + 1)).Adj i j := by
    rw [SimpleGraph.pathGraph_adj]
    constructor
    · intro hadj
      have hd := hadj.diff_dist_adj (u := a)
      rw [hdist i, hdist j] at hd
      have hne : i.val ≠ j.val := fun h => hadj.ne (congrArg f (Fin.ext h))
      omega
    · intro h
      rcases h with h | h
      · have hi : i.val < p.length := by omega
        simpa only [f, h] using p.adj_getVert_succ hi
      · have hj : j.val < p.length := by omega
        simpa only [f, h] using (p.adj_getVert_succ hj).symm
  let iso : SimpleGraph.pathGraph (p.length + 1) ≃g G :=
    { e with map_rel_iff' := hrel _ _ }
  have hcard : p.length + 1 = Fintype.card V := by
    simpa using Fintype.card_congr e
  unfold IsPathGraph
  rw [← hcard]
  exact ⟨iso.symm⟩

private lemma singleton_legal (G : SimpleGraph V) (v : V) : IsLegalMove G {v} := by
  refine ⟨Finset.singleton_nonempty _, ?_⟩
  have : (({v} : Finset V) : Set V) = {v} := by ext; simp
  rw [this]
  exact SimpleGraph.Connected.of_subsingleton

-- A shortest path covering all vertices identifies a path graph.
/-- Lemma 4.1: a connected graph that is not a path has three distinct non-cut vertices. -/
theorem three_noncut_vertices (G : SimpleGraph V) (hG : G.Connected)
    (hpath : ¬ IsPathGraph G) :
    ∃ a b c : V, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      IsNonCut G a ∧ IsNonCut G b ∧ IsNonCut G c := by
  classical
  letI := hG.nonempty
  obtain ⟨r⟩ := hG.nonempty
  have hproper (v : V) : ({v} : Finset V) ≠ Finset.univ := by
    intro h
    apply hpath
    apply path_of_shortest_cover G (SimpleGraph.Walk.nil : G.Walk v v) (by simp)
    intro x
    have hx : x ∈ ({v} : Finset V) := h ▸ Finset.mem_univ x
    simpa using hx
  obtain ⟨a, har, ha⟩ := noncut_outside G hG {r} (singleton_legal G r) (hproper r)
  obtain ⟨b, hba, hb⟩ := noncut_outside G hG {a} (singleton_legal G a) (hproper a)
  have hab : a ≠ b := by simpa [eq_comm] using hba
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist a b
  let S := p.support.toFinset
  have hS : IsLegalMove G S := by
    refine ⟨⟨a, by simp [S]⟩, ?_⟩
    have heq : (S : Set V) = {v | v ∈ p.support} := by ext v; simp [S]
    rw [heq]
    exact p.connected_induce_support
  by_cases hfull : S = Finset.univ
  · exact (hpath (path_of_shortest_cover G p hp (fun v => by
      have : v ∈ S := hfull ▸ Finset.mem_univ v
      simpa [S] using this))).elim
  · obtain ⟨c, hc, hnc⟩ := noncut_outside G hG S hS hfull
    refine ⟨a, b, c, hab, ?_, ?_, ha, hb, hnc⟩
    · intro h
      exact hc (h ▸ (by simp [S] : a ∈ S))
    · intro h
      exact hc (h ▸ (by simp [S] : b ∈ S))

/-!
## Coordinate preparation: connected cuts from a spanning tree

Construct legal cuts and expand centered states using edge differences as coordinates.
-/

private lemma reachable_induce_connected (H : SimpleGraph V) (a : V) :
    (H.induce {v | H.Reachable a v}).Connected := by
  have heq : {v | H.Reachable a v} = (H.connectedComponentMk a).supp := by
    ext v
    simp only [Set.mem_setOf_eq, SimpleGraph.ConnectedComponent.mem_supp_iff,
      SimpleGraph.ConnectedComponent.eq]
    exact SimpleGraph.reachable_comm
  rw [heq]
  exact SimpleGraph.ConnectedComponent.connected_toSimpleGraph _

private lemma bridge_cut (G : SimpleGraph V) (hG : G.Connected)
    {a b : V} (hab : G.Adj a b) (hb : G.IsBridge s(a, b)) :
    ∃ S : Finset V, IsConnectedCut G S ∧ a ∈ S ∧ b ∉ S ∧
      ∀ u v, G.Adj u v → s(u, v) ≠ s(a, b) → (u ∈ S ↔ v ∈ S) := by
  classical
  let H := G.deleteEdges {s(a, b)}
  let S := {v | H.Reachable a v}.toFinset
  have hsep : ¬ H.Reachable a b := hb
  have hparts (v : V) : H.Reachable a v ∨ H.Reachable b v := by
    obtain ⟨p⟩ := hG a v
    have step {x y : V} (q : G.Walk x y) :
        H.Reachable a x ∨ H.Reachable b x → H.Reachable a y ∨ H.Reachable b y := by
      induction q with
      | nil => exact id
      | @cons x y z hxy q ih =>
        intro hx
        apply ih
        by_cases he : s(x, y) = s(a, b)
        · rcases Sym2.eq_iff.mp he with he | he
          · exact Or.inr (by simpa only [he.2] using (SimpleGraph.Reachable.refl b (G := H)))
          · exact Or.inl (by simpa only [he.2] using (SimpleGraph.Reachable.refl a (G := H)))
        · have hh : H.Adj x y := by simpa [H] using And.intro hxy he
          exact hx.imp (fun h => h.trans hh.reachable) (fun h => h.trans hh.reachable)
    exact step p (Or.inl (SimpleGraph.Reachable.refl a))
  have hSset : (S : Set V) = {v | H.Reachable a v} := by ext; simp [S]
  have hCset : ((Finset.univ \ S : Finset V) : Set V) = {v | H.Reachable b v} := by
    ext v
    simp only [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_univ, true_and,
      S, Set.mem_toFinset, Set.mem_setOf_eq]
    constructor
    · exact fun h => (hparts v).resolve_left h
    · exact fun h hv => hsep (hv.trans h.symm)
  have hA : (G.induce (S : Set V)).Connected := by
    rw [hSset]
    exact (reachable_induce_connected H a).mono (fun _ _ h => (G.deleteEdges_le _) h)
  have hB : (G.induce ((Finset.univ \ S : Finset V) : Set V)).Connected := by
    rw [hCset]
    exact (reachable_induce_connected H b).mono (fun _ _ h => (G.deleteEdges_le _) h)
  have ha : a ∈ S := by simp [S, SimpleGraph.Reachable.refl]
  have hbS : b ∉ S := by simpa [S] using hsep
  refine ⟨S, ⟨⟨⟨a, ha⟩, hA⟩, ⟨⟨b, by simp [hbS]⟩, hB⟩⟩, ha, hbS, ?_⟩
  intro u v huv hne
  have hh : H.Adj u v := by simpa [H] using And.intro huv hne
  simp only [S, Set.mem_toFinset, Set.mem_setOf_eq]
  exact ⟨fun h => h.trans hh.reachable, fun h => h.trans hh.symm.reachable⟩

private lemma cut_mass_general (S : Finset V) [Nonempty V] : mass (cutVector S) = 0 := by
  have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
  simp [mass, cutVector, Finset.sum_sub_distrib]
  field_simp [hn] <;> ring

/-- Deleting a spanning-tree edge gives a legal connected cut; endpoint differences
are its coordinates. Expand an arbitrary real state into its mean and cut vectors. -/
private lemma connected_cut_coordinates (G : SimpleGraph V) (hG : G.Connected) :
    ∃ (a b : Fin (Fintype.card V - 1) → V) (S : Fin (Fintype.card V - 1) → Finset V),
      (∀ e, IsConnectedCut G (S e)) ∧
      ∀ z : State V, ∀ v,
        z v - mean Finset.univ z =
          ∑ e, (z (a e) - z (b e)) * cutVector (S e) v := by
  classical
  letI := hG.nonempty
  obtain ⟨T, hTG, hT⟩ := hG.exists_isTree_le
  let E := T.edgeSet
  have hex (e : E) : ∃ a b : V, s(a, b) = e.val := by
    obtain ⟨a, b⟩ := e.val
    exact ⟨a, b, rfl⟩
  choose a b heq using hex
  have hadj (e : E) : T.Adj (a e) (b e) := by
    exact T.mem_edgeSet.mp ((heq e).symm ▸ e.property)
  have hb (e : E) : T.IsBridge s(a e, b e) :=
    SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hT.isAcyclic (hadj e)
  choose S hcut ha hbS hsame using fun e => bridge_cut T hT.connected (hadj e) (hb e)
  have hdual (e f : E) : cutVector (S f) (a e) - cutVector (S f) (b e) =
      if e = f then (1 : ℝ) else 0 := by
    by_cases hef : e = f
    · subst f; simp [cutVector, ha, hbS]
    · have hne : s(a e, b e) ≠ s(a f, b f) := by
        rw [heq, heq]
        exact fun h => hef (Subtype.ext h)
      have hs := hsame f (a e) (b e) (hadj e) hne
      simp only [cutVector, hs, if_neg hef]
      ring
  have hcoordinates (z : State V) (v : V) : z v - mean Finset.univ z =
      ∑ e : E, (z (a e) - z (b e)) * cutVector (S e) v := by
    let w : State V := fun x => z x - ∑ e : E, (z (a e) - z (b e)) * cutVector (S e) x
    have hwedge (e : E) : w (a e) = w (b e) := by
      have hd : (∑ f : E, (z (a f) - z (b f)) * cutVector (S f) (a e)) -
          (∑ f : E, (z (a f) - z (b f)) * cutVector (S f) (b e)) = z (a e) - z (b e) := by
        rw [← Finset.sum_sub_distrib]
        simp_rw [← mul_sub, hdual]
        simp
      dsimp [w]
      linarith
    have hwadj {x y : V} (hxy : T.Adj x y) : w x = w y := by
      let e : E := ⟨s(x, y), T.mem_edgeSet.mpr hxy⟩
      have hpair : s(a e, b e) = s(x, y) := heq e
      rcases Sym2.eq_iff.mp hpair with hp | hp
      · simpa only [hp.1, hp.2] using hwedge e
      · simpa only [hp.1, hp.2] using (hwedge e).symm
    have hwconst (x y : V) : w x = w y := by
      obtain ⟨p⟩ := hT.connected x y
      induction p with
      | nil => rfl
      | cons h p ih => exact (hwadj h).trans ih
    have hmass : mass w = mass z := by
      simp only [mass, w, Finset.sum_sub_distrib]
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum]
      have hz (e : E) : ∑ x, cutVector (S e) x = 0 := cut_mass_general (S e)
      simp only [hz, mul_zero, Finset.sum_const_zero, sub_zero]
    have hc : w v = mean Finset.univ z := by
      have hm : (Fintype.card V : ℝ) * w v = mass z := by
        rw [← hmass]
        simp only [mass, hwconst _ v, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      unfold mean
      rw [Finset.card_univ, eq_div_iff (by exact_mod_cast Fintype.card_pos.ne')]
      simpa [mass, mul_comm] using hm
    dsimp [w] at hc
    linarith
  have hcard : Fintype.card E = Fintype.card V - 1 := by
    have ht := hT.card_edgeFinset
    rw [T.edgeFinset_card] at ht
    change Fintype.card E + 1 = Fintype.card V at ht
    omega
  -- Index the tree edges by Fin (n-1) while retaining the coordinate identity.
  let equiv : E ≃ Fin (Fintype.card V - 1) :=
    (Fintype.equivFin E).trans (finCongr hcard)
  refine ⟨a ∘ equiv.symm, b ∘ equiv.symm, S ∘ equiv.symm, ?_, ?_⟩
  · intro i
    rcases hcut (equiv.symm i) with ⟨hA, hB⟩
    exact ⟨⟨hA.1, hA.2.mono (fun _ _ h => hTG h)⟩,
      ⟨hB.1, hB.2.mono (fun _ _ h => hTG h)⟩⟩
  · intro z v
    rw [hcoordinates]
    exact (equiv.symm.sum_comp _).symm

/-!
## Rank-one algebra and the sign-reversal construction

Compute products of two-block averages and construct both signs of the required cut directions.
-/

private theorem twoBlock_entry_general (S : Finset V)
    (hs : 0 < S.card) (ht : S.card < Fintype.card V) (i j : V) :
    twoBlockMatrix S i j = 1 / (Fintype.card V : ℝ) +
      cutVector S i * cutVector S j / ((S.card : ℝ) * ((Fintype.card V : ℝ) - S.card) / Fintype.card V) := by
  have hnR : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast (lt_trans hs ht).ne'
  have hsR : (S.card : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have htR : (Fintype.card V : ℝ) - S.card ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast ht.ne')
  have hc : ((Finset.univ \ S).card : ℝ) = (Fintype.card V : ℝ) - S.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ,
      Nat.cast_sub ht.le]
  have heq : twoBlockMatrix S i j = average S (average (Finset.univ \ S) (pointMass j)) i := by
    have h := strategyMatrix_append [Finset.univ \ S] [S]
    exact (congrArg (fun M : Matrix V V ℝ => M i j) h).symm
  have hmean : mean S (average (Finset.univ \ S) (pointMass j)) = mean S (pointMass j) := by
    unfold mean
    congr 1
    apply Finset.sum_congr rfl
    intro v hv
    rw [average_apply_not_mem]
    simp [hv]
  rw [heq]
  simp only [average, hmean, cutVector]
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
    simp [hi, hj, mean, pointMass, hc] <;> field_simp [hnR, hsR, htR] <;> ring


private lemma rank_product_entry (A B : Matrix V V ℝ) (S T U W : Finset V)
    (c d : ℝ) [Nonempty V]
    (hA : ∀ i j, A i j = 1 / (Fintype.card V : ℝ) + c * cutVector S i * cutVector T j)
    (hB : ∀ i j, B i j = 1 / (Fintype.card V : ℝ) + d * cutVector U i * cutVector W j)
    (i j : V) :
    (A * B) i j = 1 / (Fintype.card V : ℝ) +
      (c * d * pairing (cutVector T) (cutVector U)) * cutVector S i * cutVector W j := by
  have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
  have hid (k : V) :
      (1 / (Fintype.card V : ℝ) + c * cutVector S i * cutVector T k) *
        (1 / (Fintype.card V : ℝ) + d * cutVector U k * cutVector W j) =
      1 / (Fintype.card V : ℝ) ^ 2 +
        (d * cutVector W j / Fintype.card V) * cutVector U k +
        (c * cutVector S i / Fintype.card V) * cutVector T k +
        (c * d * cutVector S i * cutVector W j) * (cutVector T k * cutVector U k) := by ring
  simp only [Matrix.mul_apply, hA, hB, hid, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change _ + _ * mass (cutVector U) + _ * mass (cutVector T) +
    _ * pairing (cutVector T) (cutVector U) = _
  rw [cut_mass_general, cut_mass_general]
  field_simp
  <;> ring

private lemma cut_pairing_singleton (S : Finset V) (a : V) :
    pairing (cutVector S) (cutVector {a}) = cutVector S a := by
  haveI : Nonempty V := ⟨a⟩
  simp only [pairing, cutVector, Finset.card_singleton, Nat.cast_one, mul_sub,
    Finset.sum_sub_distrib]
  have hc : ∑ v, ((if v ∈ S then 1 else 0 : ℝ) - S.card / Fintype.card V) = 0 :=
    cut_mass_general S
  rw [← Finset.sum_mul, hc, zero_mul, sub_zero]
  simp

private lemma cut_pairing_comm (S T : Finset V) :
    pairing (cutVector S) (cutVector T) = pairing (cutVector T) (cutVector S) := by
  unfold pairing
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

private noncomputable def sideSize (S : Finset V) (a : V) : ℝ :=
  if a ∈ S then (S.card : ℝ) else -((Fintype.card V : ℝ) - S.card)

private lemma sideSize_nonzero (S : Finset V) (a : V)
    (hs : 0 < S.card) (ht : S.card < Fintype.card V) : sideSize S a ≠ 0 := by
  unfold sideSize
  split_ifs
  · exact_mod_cast hs.ne'
  · exact neg_ne_zero.mpr (sub_ne_zero.mpr (by exact_mod_cast ht.ne'))

private lemma abs_sideSize_le (S : Finset V) (a : V) :
    |sideSize S a| ≤ Fintype.card V := by
  have hc : (S.card : ℝ) ≤ Fintype.card V := by exact_mod_cast S.card_le_univ
  unfold sideSize
  split_ifs
  · rw [abs_of_nonneg (by positivity)]; exact hc
  · rw [abs_neg, abs_of_nonneg (sub_nonneg.mpr hc)]
    linarith [Nat.cast_nonneg (α := ℝ) S.card]

private lemma cut_pairing_over_energy (S : Finset V) (a : V)
    (hs : 0 < S.card) (ht : S.card < Fintype.card V) :
    pairing (cutVector S) (cutVector {a}) /
      ((S.card : ℝ) * ((Fintype.card V : ℝ) - S.card) / Fintype.card V) =
        1 / sideSize S a := by
  have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast (lt_trans hs ht).ne'
  have hsR : (S.card : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have htR : (Fintype.card V : ℝ) - S.card ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast ht.ne')
  rw [cut_pairing_singleton]
  unfold cutVector sideSize
  split_ifs <;> field_simp <;> ring

private lemma connected_cut_cards (G : SimpleGraph V) (S : Finset V)
    (hS : IsConnectedCut G S) : 0 < S.card ∧ S.card < Fintype.card V := by
  refine ⟨hS.1.1.card_pos, ?_⟩
  have h := hS.2.1.card_pos
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ] at h
  omega

private lemma noncut_compl_legal (G : SimpleGraph V) (a : V) (ha : IsNonCut G a) :
    IsLegalMove G (Finset.univ \ {a}) := by
  have heq : ((Finset.univ \ {a} : Finset V) : Set V) = {v | v ≠ a} := by ext; simp
  refine ⟨?_, ?_⟩
  · obtain ⟨⟨v, hv⟩⟩ := ha.nonempty
    exact ⟨v, by simpa using hv⟩
  · rw [heq]; exact ha

private lemma twoBlock_strategy (S : Finset V) :
    strategyMatrix [Finset.univ \ S, S] = twoBlockMatrix S := by
  rw [show [Finset.univ \ S, S] = [Finset.univ \ S] ++ [S] from rfl, strategyMatrix_append]
  rfl

private lemma singleton_twoBlock_strategy (a : V) :
    strategyMatrix [Finset.univ \ {a}] = twoBlockMatrix {a} := by
  rw [← twoBlock_strategy]
  ext i j
  exact (congrFun (average_singleton a (average (Finset.univ \ {a}) (pointMass j))) i).symm

/-- Lemma 4.2's sign-reversal mechanism: insert two same-side non-cut vertices to
obtain opposite rank-one directions. The constructions have five and six moves.
This private interface uses a common six-step hull and a sufficient weaker
inverse-coefficient bound; it does not state all sharp constants of equation (4.5). -/
private lemma cut_sign_reversal (G : SimpleGraph V) (S T : Finset V)
    (hS : IsConnectedCut G S) (hT : IsConnectedCut G T)
    (a b : V) (hab : a ≠ b) (ha : IsNonCut G a) (hb : IsNonCut G b)
    (hside : a ∈ T ↔ b ∈ T) (hn : 3 ≤ Fintype.card V) :
    ∃ U Z : Matrix V V ℝ, U ∈ operatorPolytope G 6 ∧ Z ∈ operatorPolytope G 6 ∧
      ∃ k : ℝ, k ≠ 0 ∧ |k| ≤ (Fintype.card V : ℝ) ^ 2 ∧
        (∀ i j, k * (U i j - 1 / (Fintype.card V : ℝ)) = cutVector S i * cutVector T j) ∧
        (∀ i j, (-(Fintype.card V - 1 : ℝ) * k) *
          (Z i j - 1 / (Fintype.card V : ℝ)) = cutVector S i * cutVector T j) := by
  classical
  haveI : Nonempty V := ⟨a⟩
  have hnR : (3 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hn0 : (Fintype.card V : ℝ) ≠ 0 := by linarith
  have hn1 : (Fintype.card V : ℝ) - 1 ≠ 0 := by linarith
  obtain ⟨hs, hsn⟩ := connected_cut_cards G S hS
  obtain ⟨ht, htn⟩ := connected_cut_cards G T hT
  let energyOf (C : Finset V) : ℝ :=
    (C.card : ℝ) * ((Fintype.card V : ℝ) - C.card) / Fintype.card V
  let s := energyOf S
  let t := energyOf T
  let d : ℝ := ((Fintype.card V : ℝ) - 1) / Fintype.card V
  let x := sideSize S a
  let y := sideSize T a
  let k : ℝ := d * x * y
  have hd : d ≠ 0 := div_ne_zero hn1 hn0
  have hx : x ≠ 0 := sideSize_nonzero S a hs hsn
  have hy : y ≠ 0 := sideSize_nonzero T a ht htn
  have hs0 : s ≠ 0 := div_ne_zero (mul_ne_zero (by exact_mod_cast hs.ne')
    (sub_ne_zero.mpr (by exact_mod_cast hsn.ne'))) hn0
  have ht0 : t ≠ 0 := div_ne_zero (mul_ne_zero (by exact_mod_cast ht.ne')
    (sub_ne_zero.mpr (by exact_mod_cast htn.ne'))) hn0
  have hentry (C : Finset V) (hc : 0 < C.card) (hcn : C.card < Fintype.card V) (i j : V) :
      twoBlockMatrix C i j = 1 / (Fintype.card V : ℝ) +
        (1 / energyOf C) * cutVector C i * cutVector C j := by
    rw [twoBlock_entry_general C hc hcn]
    dsimp [energyOf]
    ring
  have hea (i j : V) : twoBlockMatrix {a} i j = 1 / (Fintype.card V : ℝ) +
      (1 / d) * cutVector {a} i * cutVector {a} j := by
    simpa [energyOf, d] using hentry {a} (by simp) (by simp; omega) i j
  have heb (i j : V) : twoBlockMatrix {b} i j = 1 / (Fintype.card V : ℝ) +
      (1 / d) * cutVector {b} i * cutVector {b} j := by
    simpa [energyOf, d] using hentry {b} (by simp) (by simp; omega) i j
  let A := twoBlockMatrix S * twoBlockMatrix {a}
  let U := A * twoBlockMatrix T
  let Z := A * twoBlockMatrix {b} * twoBlockMatrix T
  have hA := rank_product_entry _ _ S S {a} {a} (1 / s) (1 / d)
    (hentry S hs hsn) hea
  have hU := rank_product_entry _ _ S {a} T T
    (1 / s * (1 / d) * pairing (cutVector S) (cutVector {a})) (1 / t)
    hA (hentry T ht htn)
  have hAb := rank_product_entry _ _ S {a} {b} {b}
    (1 / s * (1 / d) * pairing (cutVector S) (cutVector {a})) (1 / d) hA heb
  have hZ := rank_product_entry _ _ S {b} T T
    ((1 / s * (1 / d) * pairing (cutVector S) (cutVector {a})) * (1 / d) *
      pairing (cutVector {a}) (cutVector {b})) (1 / t) hAb (hentry T ht htn)
  have hsa : pairing (cutVector S) (cutVector {a}) = s / x := by
    have h := cut_pairing_over_energy S a hs hsn
    change _ / s = 1 / x at h
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using (div_eq_iff hs0).mp h
  have hta : pairing (cutVector {a}) (cutVector T) = t / y := by
    rw [cut_pairing_comm]
    have h := cut_pairing_over_energy T a ht htn
    change _ / t = 1 / y at h
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using (div_eq_iff ht0).mp h
  have htb : pairing (cutVector {b}) (cutVector T) = t / y := by
    rw [← hta, cut_pairing_comm {b}, cut_pairing_comm {a}, cut_pairing_singleton,
      cut_pairing_singleton]
    simp [cutVector, hside]
  have habp : pairing (cutVector {a}) (cutVector {b}) = -1 / (Fintype.card V : ℝ) := by
    rw [cut_pairing_singleton]
    simp [cutVector, Ne.symm hab, neg_div]
  have hUmem : U ∈ operatorPolytope G 6 := by
    have heq : strategyMatrix
        (([Finset.univ \ T, T] ++ [Finset.univ \ {a}]) ++ [Finset.univ \ S, S]) = U := by
      simp only [strategyMatrix_append, twoBlock_strategy, singleton_twoBlock_strategy, U, A]
      exact (Matrix.mul_assoc _ _ _).symm
    rw [← heq]
    apply strategyMatrix_mem_polytope _ _ _ (by simp)
    intro C hC
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with ((rfl | rfl) | rfl) | (rfl | rfl)
    · exact hT.2
    · exact hT.1
    · exact noncut_compl_legal G a ha
    · exact hS.2
    · exact hS.1
  have hZmem : Z ∈ operatorPolytope G 6 := by
    have heq : strategyMatrix
        ((([Finset.univ \ T, T] ++ [Finset.univ \ {b}]) ++ [Finset.univ \ {a}]) ++
          [Finset.univ \ S, S]) = Z := by
      simp only [strategyMatrix_append, twoBlock_strategy, singleton_twoBlock_strategy, Z, A]
      simp only [Matrix.mul_assoc]
    rw [← heq]
    apply strategyMatrix_mem_polytope _ _ _ (by simp)
    intro C hC
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with (((rfl | rfl) | rfl) | rfl) | (rfl | rfl)
    · exact hT.2
    · exact hT.1
    · exact noncut_compl_legal G b hb
    · exact noncut_compl_legal G a ha
    · exact hS.2
    · exact hS.1
  refine ⟨U, Z, hUmem, hZmem, k, mul_ne_zero (mul_ne_zero hd hx) hy, ?_, ?_, ?_⟩
  · have hd1 : |d| ≤ 1 := by
      rw [abs_of_nonneg (by dsimp [d]; exact div_nonneg (by linarith) (by linarith))]
      apply (div_le_iff₀ (by linarith : (0 : ℝ) < Fintype.card V)).mpr
      linarith
    calc |k| = |d| * |x| * |y| := by simp [k, abs_mul]
         _ ≤ 1 * (Fintype.card V : ℝ) * Fintype.card V := by
           gcongr
           · exact abs_sideSize_le S a
           · exact abs_sideSize_le T a
         _ = (Fintype.card V : ℝ) ^ 2 := by ring
  · intro i j
    change k * ((A * twoBlockMatrix T) i j - _) = _
    rw [hU i j, hsa, hta]
    dsimp [k]
    field_simp
    <;> ring
  · intro i j
    change (-(Fintype.card V - 1 : ℝ) * k) *
      ((A * twoBlockMatrix {b} * twoBlockMatrix T) i j - _) = _
    rw [hZ i j, hsa, htb, habp]
    dsimp [k, d]
    field_simp
    <;> ring

private lemma signed_cut_term (G : SimpleGraph V) (S T : Finset V)
    (hS : IsConnectedCut G S) (hT : IsConnectedCut G T)
    (a b : V) (hab : a ≠ b) (ha : IsNonCut G a) (hb : IsNonCut G b)
    (hside : a ∈ T ↔ b ∈ T) (hn : 3 ≤ Fintype.card V) (B : ℝ) :
    ∃ R : Matrix V V ℝ, R ∈ operatorPolytope G 6 ∧ ∃ c : ℝ,
      0 ≤ c ∧ c ≤ (Fintype.card V : ℝ) ^ 3 * |B| ∧
        ∀ i j, c * (R i j - 1 / (Fintype.card V : ℝ)) = B * cutVector S i * cutVector T j := by
  obtain ⟨U, Z, hU, hZ, k, _, hk, hUk, hZk⟩ := cut_sign_reversal G S T hS hT a b hab ha hb hside hn
  have hnR : (3 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hk3 : |k| ≤ (Fintype.card V : ℝ) ^ 3 := by
    calc _ ≤ (Fintype.card V : ℝ) ^ 2 := hk
         _ ≤ (Fintype.card V : ℝ) ^ 3 := pow_le_pow_right₀ (by linarith) (by omega)
  have hneg : |(-(Fintype.card V - 1 : ℝ) * k)| ≤ (Fintype.card V : ℝ) ^ 3 := by
    rw [abs_mul, abs_neg, abs_of_nonneg (by linarith)]
    calc _ ≤ (Fintype.card V : ℝ) * (Fintype.card V : ℝ) ^ 2 := by gcongr; linarith
         _ = _ := by ring
  have bound (t : ℝ) (ht : |t| ≤ (Fintype.card V : ℝ) ^ 3) :
      B * t ≤ (Fintype.card V : ℝ) ^ 3 * |B| := by
    calc _ ≤ |B * t| := le_abs_self _
         _ = |B| * |t| := abs_mul _ _
         _ ≤ |B| * (Fintype.card V : ℝ) ^ 3 := mul_le_mul_of_nonneg_left ht (abs_nonneg _)
         _ = _ := mul_comm _ _
  by_cases hBk : 0 ≤ B * k
  · refine ⟨U, hU, B * k, hBk, bound k hk3, ?_⟩
    intro i j
    calc _ = B * (k * (U i j - 1 / (Fintype.card V : ℝ))) := by ring
         _ = _ := by rw [hUk]; ring
  · refine ⟨Z, hZ, B * (-(Fintype.card V - 1 : ℝ) * k), ?_, bound _ hneg, ?_⟩
    · have hprod := mul_nonneg (show 0 ≤ (Fintype.card V : ℝ) - 1 by linarith)
        (neg_nonneg.mpr (le_of_not_ge hBk))
      nlinarith
    · intro i j
      calc _ = B * ((-(Fintype.card V - 1 : ℝ) * k) *
          (Z i j - 1 / (Fintype.card V : ℝ))) := by ring
           _ = _ := by rw [hZk]; ring

private lemma consensus_mem_six (G : SimpleGraph V) (hG : G.Connected) :
    (consensusMatrix : Matrix V V ℝ) ∈ operatorPolytope G 6 := by
  have heq : strategyMatrix ([Finset.univ] : Strategy V) = consensusMatrix := by
    ext i j
    simp [strategyMatrix, run, average, mean, pointMass, consensusMatrix]
  rw [← heq]
  apply strategyMatrix_mem_polytope _ _ _ (by simp)
  intro S hS
  have h : S = Finset.univ := List.mem_singleton.mp hS
  subst S
  haveI := hG.nonempty
  refine ⟨Finset.univ_nonempty, ?_⟩
  have hset : ((Finset.univ : Finset V) : Set V) = Set.univ := by ext; simp
  rw [hset]
  exact hG.map G.induceUnivIso.symm.toHom G.induceUnivIso.symm.surjective

/-!
## Nonpath conclusion: the consensus neighborhood lies in the six-step hull

Complete the coefficient mass at consensus and apply the cut-coordinate estimates to prove Proposition 4.3.
-/

/-- Complete nonnegative coefficients of total mass at most one by assigning the
remaining weight to the center matrix. Shared by the path and nonpath decompositions. -/
private lemma convex_decomposition_of_deviations {ι : Type*} [Fintype ι]
    (K : Set (Matrix V V ℝ)) (hK : Convex ℝ K) (J M : Matrix V V ℝ)
    (hJ : J ∈ K) (c : ι → ℝ) (R : ι → Matrix V V ℝ)
    (hc : ∀ p, 0 ≤ c p) (hsum : ∑ p, c p ≤ 1) (hR : ∀ p, R p ∈ K)
    (hexp : ∀ i j, ∑ p, c p * (R p i j - J i j) = M i j - J i j) : M ∈ K := by
  let weights : Option ι → ℝ := Option.elim' (1 - ∑ p, c p) c
  let matrices : Option ι → Matrix V V ℝ := Option.elim' J R
  have hw : ∀ p, 0 ≤ weights p := by
    intro p; cases p with
    | none => exact sub_nonneg.mpr hsum
    | some p => exact hc p
  have hm : ∀ p, matrices p ∈ K := by
    intro p; cases p with
    | none => exact hJ
    | some p => exact hR p
  have hcombo := hK.sum_mem (fun p _ => hw p)
    (show ∑ p, weights p = 1 by simp [weights]) (fun p _ => hm p)
  convert hcombo using 1
  ext i j
  have h := hexp i j
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul] at h
  simp only [Fintype.sum_option, weights, matrices, Option.elim',
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  linarith

/-- Proposition 4.3: every matrix in the affine row/column-sum space within the stated
radius of consensus belongs to the hull of strategies of length at most six. -/
theorem nonpath_local_decomposition (G : SimpleGraph V) (hG : G.Connected)
    (hpath : ¬ IsPathGraph G) (M : Matrix V V ℝ)
    (hM : M ∈ affineStochastic)
    (hnear : maxEntryNorm (M - consensusMatrix) ≤ localRadius (Fintype.card V)) :
    M ∈ operatorPolytope G 6 := by
  classical
  obtain ⟨x, y, z, hxy, hxz, hyz, hx, hy, hz⟩ := three_noncut_vertices G hG hpath
  have hn : 3 ≤ Fintype.card V := by
    have h := (Finset.card_le_univ ({x, y, z} : Finset V))
    simpa [hxy, hxz, hyz] using h
  have hnR : (3 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hn0 : (Fintype.card V : ℝ) ≠ 0 := by linarith
  obtain ⟨a, b, S, hS, hcoords⟩ := connected_cut_coordinates G hG
  let E := Fin (Fintype.card V - 1)
  let B (p : E × E) : ℝ :=
    M (a p.1) (a p.2) - M (b p.1) (a p.2) - M (a p.1) (b p.2) + M (b p.1) (b p.2)
  have hpair (T : Finset V) : ∃ u v : V, u ≠ v ∧ IsNonCut G u ∧ IsNonCut G v ∧
      (u ∈ T ↔ v ∈ T) := by
    by_cases hxT : x ∈ T <;> by_cases hyT : y ∈ T <;> by_cases hzT : z ∈ T
    all_goals first
      | exact ⟨x, y, hxy, hx, hy, by tauto⟩
      | exact ⟨x, z, hxz, hx, hz, by tauto⟩
      | exact ⟨y, z, hyz, hy, hz, by tauto⟩
  have hterms (p : E × E) : ∃ R : Matrix V V ℝ, R ∈ operatorPolytope G 6 ∧ ∃ c : ℝ,
      0 ≤ c ∧ c ≤ (Fintype.card V : ℝ) ^ 3 * |B p| ∧
        ∀ i j, c * (R i j - 1 / (Fintype.card V : ℝ)) =
          B p * cutVector (S p.1) i * cutVector (S p.2) j := by
    obtain ⟨u, v, huv, hu, hv, ht⟩ := hpair (S p.2)
    exact signed_cut_term G (S p.1) (S p.2) (hS _) (hS _) u v huv hu hv ht hn (B p)
  choose R hR c hc0 hcb hceq using hterms
  have hexp (i j : V) : M i j - 1 / (Fintype.card V : ℝ) =
      ∑ p : E × E, B p * cutVector (S p.1) i * cutVector (S p.2) j := by
    have hmcol : mean Finset.univ (fun v => M v j) = 1 / (Fintype.card V : ℝ) := by
      simp [mean, hM.2 j]
    have hcol := hcoords (fun v => M v j) i
    rw [hmcol] at hcol
    rw [hcol, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro e _
    have hmrow : mean Finset.univ (fun v => M (a e) v - M (b e) v) = 0 := by
      simp [mean, Finset.sum_sub_distrib, hM.1]
    have hrow := hcoords (fun v => M (a e) v - M (b e) v) j
    rw [hmrow, sub_zero] at hrow
    rw [hrow, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro f _
    dsimp [B]
    ring
  let Λ : ℝ := ∑ p, c p
  have hentry (i j : V) : |M i j - 1 / (Fintype.card V : ℝ)| ≤ maxEntryNorm (M - consensusMatrix) := by
    unfold maxEntryNorm
    change |M i j - 1 / (Fintype.card V : ℝ)| ≤
      ‖(fun p : V × V => M p.1 p.2 - 1 / (Fintype.card V : ℝ))‖
    simpa only [Real.norm_eq_abs] using
      norm_le_pi_norm (fun p : V × V => M p.1 p.2 - 1 / (Fintype.card V : ℝ)) (i, j)
  have hB (p : E × E) : |B p| ≤ 4 * maxEntryNorm (M - consensusMatrix) := by
    have h1 := (abs_le.mp (hentry (a p.1) (a p.2)))
    have h2 := (abs_le.mp (hentry (b p.1) (a p.2)))
    have h3 := (abs_le.mp (hentry (a p.1) (b p.2)))
    have h4 := (abs_le.mp (hentry (b p.1) (b p.2)))
    apply abs_le.mpr
    dsimp [B]
    constructor <;> linarith
  have hΛ : Λ ≤ 1 := by
    have hnsub : ((Fintype.card V - 1 : ℕ) : ℝ) ≤ Fintype.card V := by exact_mod_cast Nat.sub_le (Fintype.card V) 1
    calc
      Λ ≤ ∑ p : E × E, (Fintype.card V : ℝ) ^ 3 * (4 * maxEntryNorm (M - consensusMatrix)) := by
        apply Finset.sum_le_sum
        intro p _
        exact (hcb p).trans (mul_le_mul_of_nonneg_left (hB p) (by positivity))
      _ = ((Fintype.card V - 1 : ℕ) : ℝ) ^ 2 *
          ((Fintype.card V : ℝ) ^ 3 * (4 * maxEntryNorm (M - consensusMatrix))) := by
        simp [E, pow_two, mul_assoc]
      _ ≤ (Fintype.card V : ℝ) ^ 2 *
          ((Fintype.card V : ℝ) ^ 3 * (4 * localRadius (Fintype.card V))) := by
        have hnorm : 0 ≤ maxEntryNorm (M - consensusMatrix) := norm_nonneg _
        gcongr
      _ = 1 := by unfold localRadius; field_simp
  apply convex_decomposition_of_deviations _ (convex_convexHull ℝ _) consensusMatrix M
    (consensus_mem_six G hG) c R hc0 hΛ hR
  intro i j
  simpa only [consensusMatrix, hceq] using (hexp i j).symm

/-!
## Path definitions: ordered minors, mixed differences, and the monotone cone

The path proof uses total nonnegativity and centered monotonicity to control signs in a convex expansion.
-/

/-- Every minor chosen by increasing row and column embeddings has nonnegative determinant. -/
def TotallyNonnegative {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ k : ℕ, ∀ r c : Fin k → Fin n, StrictMono r → StrictMono c →
    0 ≤ Matrix.det (M.submatrix r c)

/-- Adjacent mixed differences of the matrix entries, giving its prefix-cut expansion coefficients. -/
noncomputable def mixedDifferences {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ :=
  fun i j =>
    M ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ -
    M ⟨i.val + 1, by omega⟩ ⟨j.val, by omega⟩ -
    M ⟨i.val, by omega⟩ ⟨j.val + 1, by omega⟩ +
    M ⟨i.val + 1, by omega⟩ ⟨j.val + 1, by omega⟩

/-- The sum of absolute coordinates, used for the quantitative monotone-cone estimates. -/
noncomputable def normOne {n : ℕ} (w : State (Fin n)) : ℝ := ∑ i, |w i|

/-- Nonincreasing real vectors whose coordinate sum is zero. -/
def centeredMonotoneCone (n : ℕ) : Set (State (Fin n)) :=
  {w | Antitone w ∧ mass w = 0}

/-!
## Path preparation: total nonnegativity and ratio estimates

Prove Lemma 5.2 by preserving ordered minors, then obtain the near-monotone estimate of Lemma 5.3.
-/

private theorem tnn_one (n : ℕ) : TotallyNonnegative (1 : Matrix (Fin n) (Fin n) ℝ) := by
  classical
  intro k r c hr hc
  by_cases hrc : r = c
  · subst c
    have heq : (1 : Matrix (Fin n) (Fin n) ℝ).submatrix r r = 1 := by
      ext i j
      simp [Matrix.submatrix_apply, Matrix.one_apply, hr.injective.eq_iff]
    rw [heq, Matrix.det_one]
    norm_num
  · have hmissing : ∃ i, ∀ j, r i ≠ c j := by
      by_contra! h
      have hsub : Finset.univ.image r ⊆ Finset.univ.image c := by
        intro v hv
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
        obtain ⟨j, hj⟩ := h i
        exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj.symm⟩
      have heq := Finset.eq_of_subset_of_card_le hsub (by
        simp [Finset.card_image_of_injective _ hr.injective,
          Finset.card_image_of_injective _ hc.injective])
      have hset : Set.range r = Set.range c := by
        simpa using congrArg (fun s : Finset (Fin n) => (s : Set (Fin n))) heq
      exact hrc ((hr.range_inj hc).mp hset)
    obtain ⟨i, hi⟩ := hmissing
    rw [Matrix.det_eq_zero_of_row_eq_zero i (fun j => by
      simp [Matrix.submatrix_apply, Matrix.one_apply, hi j])]

/-- Interval averaging preserves total nonnegativity. Two averaged rows give a zero
minor; one averaged row gives a nonnegative average of order-preserving old minors. -/
private theorem tnn_average_interval {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : TotallyNonnegative M) (a b : Fin n) :
    TotallyNonnegative (fun i j => average (Finset.Icc a b) (fun v => M v j) i) := by
  classical
  intro k r c hr hc
  let S := Finset.Icc a b
  let N : Matrix (Fin n) (Fin n) ℝ := fun i j => average S (fun v => M v j) i
  change 0 ≤ (N.submatrix r c).det
  by_cases hdup : ∃ i j, i ≠ j ∧ r i ∈ S ∧ r j ∈ S
  · obtain ⟨i, j, hij, hi, hj⟩ := hdup
    rw [Matrix.det_zero_of_row_eq hij (by
      funext l
      simp [N, Matrix.submatrix_apply, average, hi, hj])]
  · by_cases hex : ∃ p, r p ∈ S
    · obtain ⟨p, hp⟩ := hex
      have hnot (i : Fin k) (hi : i ≠ p) : r i ∉ S :=
        fun hri => hdup ⟨i, p, hi, hri, hp⟩
      let row (v : Fin n) : Fin k → ℝ := fun j => M v (c j)
      have heq : N.submatrix r c =
          (M.submatrix r c).updateRow p ((S.card : ℝ)⁻¹ • ∑ v ∈ S, row v) := by
        ext i j
        by_cases hi : i = p
        · subst i
          simp [Matrix.submatrix_apply, Matrix.updateRow_apply, N, average, hp,
            mean, row, Finset.sum_apply, Pi.smul_apply, div_eq_mul_inv, mul_comm]
        · simp [Matrix.submatrix_apply, Matrix.updateRow_apply, N, average, hnot i hi, hi]
      rw [heq, Matrix.det_updateRow_smul]
      have hsum := (Matrix.detRowAlternating : (Fin k → ℝ) [⋀^Fin k]→ₗ[ℝ] ℝ).toMultilinearMap.map_update_sum
        S p row (M.submatrix r c)
      change Matrix.det ((M.submatrix r c).updateRow p (∑ v ∈ S, row v)) =
        ∑ v ∈ S, Matrix.det ((M.submatrix r c).updateRow p (row v)) at hsum
      rw [hsum]
      apply mul_nonneg (by positivity)
      apply Finset.sum_nonneg
      intro v hv
      have hr' : StrictMono (Function.update r p v) := by
        intro i j hij
        have hvi : a ≤ v ∧ v ≤ b := Finset.mem_Icc.mp hv
        have hpi : a ≤ r p ∧ r p ≤ b := Finset.mem_Icc.mp hp
        by_cases hi : i = p
        · subst i
          have hj : j ≠ p := ne_of_gt hij
          have hbj : b < r j := by
            apply lt_of_not_ge
            intro hle
            exact hnot j hj (Finset.mem_Icc.mpr ⟨hpi.1.trans (hr hij).le, hle⟩)
          simpa [Function.update_of_ne hj] using hvi.2.trans_lt hbj
        · by_cases hj : j = p
          · subst j
            have hia : r i < a := by
              apply lt_of_not_ge
              intro hle
              exact hnot i hi (Finset.mem_Icc.mpr ⟨hle, (hr hij).le.trans hpi.2⟩)
            simpa [Function.update_of_ne hi] using hia.trans_le hvi.1
          · simpa [Function.update_of_ne hi, Function.update_of_ne hj] using hr hij
      have hup : (M.submatrix r c).updateRow p (row v) =
          M.submatrix (Function.update r p v) c := by
        ext i j
        by_cases hi : i = p <;> simp [Matrix.updateRow_apply, Matrix.submatrix_apply, row, hi]
      rw [hup]
      exact hM k _ c hr' hc
    · have heq : N.submatrix r c = M.submatrix r c := by
        ext i j
        simp [N, Matrix.submatrix_apply, average, show r i ∉ S from fun hi => hex ⟨i, hi⟩]
      rw [heq]
      exact hM k r c hr hc

/-- Lemma 5.2: every path strategy matrix has all ordered minors nonnegative. -/
theorem path_strategy_totallyNonnegative (n : ℕ) (σ : Strategy (Fin n))
    (hσ : IsLegal (SimpleGraph.pathGraph n) σ) : TotallyNonnegative (strategyMatrix σ) := by
  revert hσ
  induction σ using List.reverseRecOn with
  | nil =>
    intro _
    have heq : strategyMatrix ([] : Strategy (Fin n)) = 1 := by
      ext i j
      simp [strategyMatrix, run, pointMass, Matrix.one_apply, eq_comm]
    rw [heq]
    exact tnn_one n
  | append_singleton σ S ih =>
    intro hσ
    have hpre : IsLegal (SimpleGraph.pathGraph n) σ := fun T hT => hσ T (by simp [hT])
    have hS : IsLegalMove (SimpleGraph.pathGraph n) S := hσ S (by simp)
    have heq : strategyMatrix (σ ++ [S]) =
        fun i j => average S (fun v => strategyMatrix σ v j) i := by
      ext i j
      simp [strategyMatrix, run_append]
    rw [heq]
    obtain ⟨a, b, _, rfl⟩ := (path_legal_iff_interval S).mp hS
    exact tnn_average_interval (strategyMatrix σ) (ih hpre) a b

/-- Lemma 5.3: positive probability vectors with a nonincreasing coordinate ratio give
the required near-monotone difference estimate. -/
theorem ratio_near_monotone (n : ℕ) (hn : 1 ≤ n) (a b : State (Fin n))
    (ha : ∀ j, 0 < a j) (hb : ∀ j, 0 < b j) (hma : mass a = 1) (hmb : mass b = 1)
    (hratio : Antitone fun j => a j / b j) (η : ℝ) (hη : 0 ≤ η) (hη1 : η < 1)
    (hnear : ∀ j, |(n : ℝ) * b j - 1| ≤ η) :
    ∃ z ∈ centeredMonotoneCone n, normOne (a - b - z) ≤ 2 * η / (1 - η) * normOne (a - b) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hden : 0 < 1 - η := sub_pos.mpr hη1
  let t : State (Fin n) := fun j => a j / b j - 1
  let tbar : ℝ := (∑ j, t j) / n
  let z : State (Fin n) := fun j => (t j - tbar) / n
  have hbt (j : Fin n) : b j * t j = a j - b j := by
    dsimp [t]; field_simp [ne_of_gt (hb j)]
  have hsum : ∑ j, b j * t j = 0 := by
    simp_rw [hbt]
    simpa [mass, Finset.sum_sub_distrib] using sub_eq_zero.mpr (hma.trans hmb.symm)
  have hnear' (j : Fin n) : |b j - 1 / (n : ℝ)| ≤ η / n := by
    have hid : b j - 1 / (n : ℝ) = ((n : ℝ) * b j - 1) / n := by
      field_simp
    rw [hid, abs_div, abs_of_pos hnR]
    exact div_le_div_of_nonneg_right (hnear j) hnR.le
  have hlow (j : Fin n) : (1 - η) / (n : ℝ) ≤ b j := by
    apply (div_le_iff₀ hnR).mpr
    have := (abs_le.mp (hnear j)).1
    nlinarith
  have hbar : |tbar| ≤ η / (n : ℝ) * ∑ j, |t j| := by
    have heq : tbar = ∑ j, (1 / (n : ℝ) - b j) * t j := by
      simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, sub_zero]
      dsimp [tbar]; ring
    rw [heq, Finset.mul_sum]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j _
    rw [abs_mul, abs_sub_comm]
    exact mul_le_mul_of_nonneg_right (hnear' j) (abs_nonneg _)
  have ht : (∑ j, |t j|) ≤ (n : ℝ) / (1 - η) * normOne (a - b) := by
    have hle : (1 - η) / (n : ℝ) * (∑ j, |t j|) ≤ normOne (a - b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      change (1 - η) / (n : ℝ) * |t j| ≤ |a j - b j|
      rw [← hbt, abs_mul, abs_of_pos (hb j)]
      exact mul_le_mul_of_nonneg_right (hlow j) (abs_nonneg _)
    calc
      (∑ j, |t j|) ≤ normOne (a - b) / ((1 - η) / (n : ℝ)) :=
        (le_div_iff₀ (div_pos hden hnR)).mpr (by simpa only [mul_comm] using hle)
      _ = (n : ℝ) / (1 - η) * normOne (a - b) := by
        field_simp [hnR.ne', hden.ne']
  refine ⟨z, ⟨?_, ?_⟩, ?_⟩
  · intro i j hij
    change (a j / b j - 1 - tbar) / n ≤ (a i / b i - 1 - tbar) / n
    exact div_le_div_of_nonneg_right
      (sub_le_sub_right (sub_le_sub_right (hratio hij) 1) tbar) hnR.le
  · change (∑ j, (t j - tbar) / (n : ℝ)) = 0
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    dsimp [tbar]
    field_simp <;> ring
  · have heq (j : Fin n) : (a - b - z) j =
        (b j - 1 / (n : ℝ)) * t j + tbar / n := by
      change a j - b j - (t j - tbar) / n = _
      rw [← hbt]
      ring
    calc
      normOne (a - b - z) ≤
          ∑ j : Fin n, (η / (n : ℝ) * |t j| + |tbar| / n) := by
        apply Finset.sum_le_sum
        intro j _
        rw [heq]
        apply (abs_add_le _ _).trans
        rw [abs_mul, abs_div, abs_of_pos hnR]
        exact add_le_add (mul_le_mul_of_nonneg_right (hnear' j) (abs_nonneg _)) le_rfl
      _ = η / (n : ℝ) * (∑ j, |t j|) + |tbar| := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
      _ ≤ 2 * η / (n : ℝ) * (∑ j, |t j|) := by
        calc
          _ ≤ η / (n : ℝ) * (∑ j, |t j|) + η / (n : ℝ) * (∑ j, |t j|) :=
            add_le_add le_rfl hbar
          _ = _ := by ring
      _ ≤ 2 * η / (n : ℝ) * ((n : ℝ) / (1 - η) * normOne (a - b)) :=
        mul_le_mul_of_nonneg_left ht (by positivity)
      _ = 2 * η / (1 - η) * normOne (a - b) := by field_simp

/-!
## Path preparation: cut expansions, energy, and cone angles

Develop prefix-cut inner products and their Gram matrix, then prove the Poincare estimate and Lemma 5.4.
-/

private theorem cut_mass {n : ℕ} (hn : 0 < n) (S : Finset (Fin n)) :
    mass (cutVector S) = 0 := by
  letI : NeZero n := ⟨hn.ne'⟩
  exact cut_mass_general S

private theorem cut_pairing {n : ℕ} (hn : 0 < n) (S T : Finset (Fin n)) :
    pairing (cutVector S) (cutVector T) =
      ((S ∩ T).card : ℝ) - (S.card : ℝ) * T.card / n := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hind (v : Fin n) :
      (if v ∈ S then 1 else 0 : ℝ) * (if v ∈ T then 1 else 0) =
        if v ∈ S ∩ T then 1 else 0 := by
    by_cases hs : v ∈ S <;> by_cases ht : v ∈ T <;> simp [hs, ht]
  simp only [pairing, cutVector, sub_mul, mul_sub, Finset.sum_sub_distrib,
    hind, ← Finset.sum_mul, ← Finset.mul_sum]
  simp only [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp <;> ring

private theorem normOne_cut_le {n : ℕ} (hn : 0 < n) (S : Finset (Fin n)) :
    normOne (cutVector S) ≤ 2 * S.card := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    normOne (cutVector S) ≤
        ∑ v : Fin n, ((if v ∈ S then 1 else 0 : ℝ) + (S.card : ℝ) / n) := by
      apply Finset.sum_le_sum
      intro v _
      simp only [cutVector, Fintype.card_fin]
      change |(if v ∈ S then 1 else 0 : ℝ) - (S.card : ℝ) / n| ≤ _
      calc
        _ ≤ |(if v ∈ S then 1 else 0 : ℝ)| + |(S.card : ℝ) / n| := by
          simpa only [sub_eq_add_neg, abs_neg] using
            abs_add_le (if v ∈ S then 1 else 0 : ℝ) (-((S.card : ℝ) / n))
        _ = _ := by
          have hi : (0 : ℝ) ≤ if v ∈ S then 1 else 0 := by split_ifs <;> norm_num
          rw [abs_of_nonneg hi, abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hnR.le)]
    _ = 2 * S.card := by
      simp [Finset.sum_add_distrib, two_mul]
      field_simp

private theorem cut_compl {n : ℕ} (hn : 0 < n) (S : Finset (Fin n)) :
    cutVector (Finset.univ \ S) = -cutVector S := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hc : S.card ≤ n := by simpa using S.card_le_univ
  funext v
  simp only [cutVector, Finset.card_sdiff_of_subset (Finset.subset_univ S),
    Finset.card_univ, Fintype.card_fin, Nat.cast_sub hc, Pi.neg_apply]
  by_cases hv : v ∈ S <;> simp [hv] <;> field_simp <;> ring

private theorem normOne_cut_compl_le {n : ℕ} (hn : 0 < n) (S : Finset (Fin n)) :
    normOne (cutVector S) ≤ 2 * ((n : ℝ) - S.card) := by
  have h := normOne_cut_le hn (Finset.univ \ S)
  have hc : S.card ≤ n := by simpa using S.card_le_univ
  simpa [cut_compl hn, normOne, Finset.card_sdiff_of_subset (Finset.subset_univ S),
    Nat.cast_sub hc] using h

/-- Prove the nested-prefix estimate for general nested sets first, to reuse it in coordinate expansions. -/
private theorem nested_cut_angle {n : ℕ} (hn : 0 < n) (S T : Finset (Fin n))
    (hst : S ⊆ T) : normOne (cutVector S) * normOne (cutVector T) ≤
      4 * (n : ℝ) * pairing (cutVector S) (cutVector T) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  calc
    normOne (cutVector S) * normOne (cutVector T) ≤
        (2 * (S.card : ℝ)) * (2 * ((n : ℝ) - T.card)) := by
      apply mul_le_mul (normOne_cut_le hn S) (normOne_cut_compl_le hn T)
      · exact Finset.sum_nonneg fun _ _ => abs_nonneg _
      · positivity
    _ = 4 * (n : ℝ) * pairing (cutVector S) (cutVector T) := by
      rw [cut_pairing hn, Finset.inter_eq_left.mpr hst]
      field_simp <;> ring

private theorem prefix_cut_jump {m : ℕ} (p i : Fin m) :
    cutVector (Finset.Iic i.castSucc) p.castSucc -
      cutVector (Finset.Iic i.castSucc) p.succ = if p = i then 1 else 0 := by
  simp only [cutVector, Finset.mem_Iic, Fin.le_def, Fin.val_castSucc,
    Fin.val_succ, Fin.ext_iff]
  split_ifs <;> first | omega | ring

private theorem monotone_cut_expansion (m : ℕ) (z : State (Fin (m + 1)))
    (hz : mass z = 0) :
    z = fun j => ∑ p : Fin m, (z p.castSucc - z p.succ) *
      cutVector (Finset.Iic p.castSucc) j := by
  let u : State (Fin (m + 1)) := fun j => ∑ p : Fin m,
    (z p.castSucc - z p.succ) * cutVector (Finset.Iic p.castSucc) j
  have hu (p : Fin m) : u p.castSucc - u p.succ = z p.castSucc - z p.succ := by
    dsimp [u]
    rw [← Finset.sum_sub_distrib]
    simp_rw [← mul_sub, prefix_cut_jump]
    simp
  have hconst (j : Fin (m + 1)) : z j - u j = z 0 - u 0 := by
    induction j using Fin.induction with
    | zero => rfl
    | succ p ih => have := hu p; linarith
  have humass : mass u = 0 := by
    unfold mass
    dsimp [u]
    rw [Finset.sum_comm]
    have hm (p : Fin m) : ∑ j, cutVector (Finset.Iic p.castSucc) j = 0 :=
      cut_mass (by omega) _
    simp_rw [← Finset.mul_sum, hm]
    simp
  have hzero : z 0 - u 0 = 0 := by
    have heq : ((m + 1 : ℕ) : ℝ) * (z 0 - u 0) = 0 := by
      calc
        _ = ∑ j : Fin (m + 1), (z j - u j) := by simp_rw [hconst]; simp [mul_sub]
        _ = 0 := by rw [Finset.sum_sub_distrib]; exact sub_eq_zero.mpr (hz.trans humass.symm)
    exact (mul_eq_zero.mp heq).resolve_left (by positivity)
  funext j
  have := hconst j
  change z j = u j
  linarith

private theorem normOne_sum_le {m n : ℕ} (c : Fin m → ℝ) (u : Fin m → State (Fin n))
    (hc : ∀ p, 0 ≤ c p) :
    normOne (fun j => ∑ p, c p * u p j) ≤ ∑ p, c p * normOne (u p) := by
  calc
    _ ≤ ∑ j : Fin n, ∑ p : Fin m, |c p * u p j| :=
      Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      rw [Finset.sum_comm]
      simp_rw [abs_mul, abs_of_nonneg (hc _), ← Finset.mul_sum, normOne]

/-- Expand the pairing of two finite linear combinations. Shared by the energy and cone estimates. -/
private lemma pairing_sum_smul {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → ℝ) (d : κ → ℝ) (u : ι → State V) (v : κ → State V) :
    pairing (fun x => ∑ i, c i * u i x) (fun x => ∑ j, d j * v j x) =
      ∑ i, ∑ j, c i * d j * pairing (u i) (v j) := by
  have hu : (fun x => ∑ i, c i * u i x) = ∑ i, c i • u i := by
    ext x; simp
  have hv : (fun x => ∑ j, d j * v j x) = ∑ j, d j • v j := by
    ext x; simp
  rw [hu, hv]
  change (∑ i, c i • u i) ⬝ᵥ (∑ j, d j • v j) =
    ∑ i, ∑ j, c i * d j * (u i ⬝ᵥ v j)
  simp only [sum_dotProduct, dotProduct_sum, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp only [mul_comm]

private lemma sum_fin_value (m : ℕ) : ∑ i : Fin m, (i.val : ℝ) = (m : ℝ) * (m - 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih => simp only [Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last, ih, Nat.cast_add, Nat.cast_one]; ring

private lemma prefix_linear_sum (m : ℕ) (p : Fin m) :
    ∑ v ∈ Finset.Iic p.castSucc, ((m : ℝ) / 2 - v.val) =
      ((p.val : ℝ) + 1) * ((m : ℝ) - p.val) / 2 := by
  have hsum : ∑ v ∈ Finset.Iic p.castSucc, (v.val : ℝ) =
      ((p.val : ℝ) + 1) * p.val / 2 := by
    have h := Finset.sum_map (Finset.Iic p.castSucc) Fin.valEmbedding (fun k : ℕ => (k : ℝ))
    rw [Fin.map_valEmbedding_Iic] at h
    simp only [Fin.val_castSucc] at h
    have hrange : (Finset.Iic p.val : Finset ℕ) = Finset.range (p.val + 1) := by ext; simp
    rw [hrange] at h
    have hf := sum_fin_value (p.val + 1)
    rw [Fin.sum_univ_eq_sum_range] at hf
    simpa using h.symm.trans hf
  rw [Finset.sum_sub_distrib, Finset.sum_const, Fin.card_Iic, Fin.val_castSucc, nsmul_eq_mul, hsum]
  push_cast
  ring

private lemma prefix_gram_row_sum (m : ℕ) (p : Fin m) :
    ∑ q : Fin m, pairing (cutVector (Finset.Iic p.castSucc))
      (cutVector (Finset.Iic q.castSucc)) =
        ((p.val : ℝ) + 1) * ((m : ℝ) - p.val) / 2 := by
  let z : State (Fin (m + 1)) := fun v => (m : ℝ) / 2 - v.val
  have hz : mass z = 0 := by
    simp only [mass, z, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, sum_fin_value, Nat.cast_add, Nat.cast_one]
    ring
  have hexp (v : Fin (m + 1)) : ∑ q : Fin m, cutVector (Finset.Iic q.castSucc) v = z v := by
    have h := congrFun (monotone_cut_expansion m z hz) v
    have hdiff (q : Fin m) : z q.castSucc - z q.succ = 1 := by
      simp only [z, Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one]
      ring
    simpa only [hdiff, one_mul] using h.symm
  calc
    _ = pairing (cutVector (Finset.Iic p.castSucc)) z := by
      simp only [pairing]
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, hexp]
    _ = ∑ v ∈ Finset.Iic p.castSucc, z v := by
      simp only [pairing, cutVector, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
      change (∑ v, (if v ∈ Finset.Iic p.castSucc then 1 else 0 : ℝ) * z v) - _ * mass z = _
      rw [hz]
      simp only [mul_zero, sub_zero, ite_mul, one_mul, zero_mul, ← Finset.sum_filter,
        Finset.filter_mem_eq_inter, Finset.univ_inter]
    _ = _ := prefix_linear_sum m p

private lemma prefix_gram_nonneg (m : ℕ) (p q : Fin m) :
    0 ≤ pairing (cutVector (Finset.Iic p.castSucc)) (cutVector (Finset.Iic q.castSucc)) := by
  wlog hpq : p ≤ q generalizing p q
  · simpa [pairing, mul_comm] using this q p (le_of_not_ge hpq)
  rw [cut_pairing (by omega), Finset.inter_eq_left.mpr (Finset.Iic_subset_Iic.mpr (by simpa using hpq))]
  simp only [Fin.card_Iic, Fin.val_castSucc]
  push_cast
  have hnR : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hq : (q.val : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast (show q.val + 1 ≤ m + 1 by omega)
  apply (sub_nonneg.mpr ?_)
  apply (div_le_iff₀ hnR).mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) p.val]

/-- The discrete Poincare estimate used in Lemma 2.2: centered energy is at most
n^2/8 times the sum of squared adjacent differences. Prefix-cut Gram matrix
row sums give the constant, without a monotonicity assumption on the state. -/
theorem path_variance_le_gap_energy (m : ℕ) (w : State (Fin (m + 1))) :
    centeredEnergy w ≤ (((m + 1 : ℕ) : ℝ) ^ 2 / 8) *
      ∑ p : Fin m, (w p.castSucc - w p.succ) ^ 2 := by
  let z : State (Fin (m + 1)) := fun v => w v - mean Finset.univ w
  let d (p : Fin m) : ℝ := w p.castSucc - w p.succ
  let K (p q : Fin m) : ℝ :=
    pairing (cutVector (Finset.Iic p.castSucc)) (cutVector (Finset.Iic q.castSucc))
  have hz : mass z = 0 := by
    simp only [mass, z, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact sub_eq_zero.mpr (card_mul_mean Finset.univ w).symm
  have hez : z = fun j => ∑ p : Fin m, d p * cutVector (Finset.Iic p.castSucc) j := by
    simpa only [z, sub_sub_sub_cancel_right, d] using monotone_cut_expansion m z hz
  have henergy : energy z = ∑ p : Fin m, ∑ q : Fin m, d p * d q * K p q := by
    have h := pairing_sum_smul d d (fun p => cutVector (Finset.Iic p.castSucc))
      (fun p => cutVector (Finset.Iic p.castSucc))
    rw [← hez] at h
    simpa only [K, pairing, energy, pow_two] using h
  have hsym (p q : Fin m) : K p q = K q p := by simp [K, pairing, mul_comm]
  have hrow (p : Fin m) : ∑ q : Fin m, K p q ≤ ((m + 1 : ℕ) : ℝ) ^ 2 / 8 := by
    rw [show (∑ q, K p q) = _ from prefix_gram_row_sum m p]
    push_cast
    nlinarith [sq_nonneg ((m : ℝ) - 2 * p.val - 1)]
  change energy z ≤ _
  calc
    energy z = ∑ p : Fin m, ∑ q : Fin m, d p * d q * K p q := henergy
    _ ≤ ∑ p : Fin m, ∑ q : Fin m, ((d p ^ 2 + d q ^ 2) / 2) * K p q := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro q _
      apply mul_le_mul_of_nonneg_right _ (prefix_gram_nonneg m p q)
      nlinarith [sq_nonneg (d p - d q)]
    _ = ∑ p : Fin m, d p ^ 2 * (∑ q : Fin m, K p q) := by
      simp only [add_div, add_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
      have heq : (∑ p : Fin m, ∑ q : Fin m, d q ^ 2 / 2 * K p q) =
          ∑ p : Fin m, d p ^ 2 / 2 * (∑ q : Fin m, K p q) := by
        rw [Finset.sum_comm]
        simp only [hsym, ← Finset.mul_sum]
      rw [heq, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ ≤ ∑ p : Fin m, d p ^ 2 * (((m + 1 : ℕ) : ℝ) ^ 2 / 8) := by
      exact Finset.sum_le_sum (fun p _ => mul_le_mul_of_nonneg_left (hrow p) (sq_nonneg _))
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

/-- Lemma 5.4: a quantitative lower bound on pairings within the centered monotone cone. -/
theorem monotone_cone_angle (n : ℕ) (hn : 1 ≤ n) (z w : State (Fin n))
    (hz : z ∈ centeredMonotoneCone n) (hw : w ∈ centeredMonotoneCone n) :
    1 / (4 * (n : ℝ)) * normOne z * normOne w ≤ pairing z w := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let c : Fin m → ℝ := fun p => z p.castSucc - z p.succ
  let d : Fin m → ℝ := fun p => w p.castSucc - w p.succ
  let u : Fin m → State (Fin (m + 1)) := fun p => cutVector (Finset.Iic p.castSucc)
  have hc (p : Fin m) : 0 ≤ c p := sub_nonneg.mpr (hz.1 (by simp [Fin.le_def]))
  have hd (p : Fin m) : 0 ≤ d p := sub_nonneg.mpr (hw.1 (by simp [Fin.le_def]))
  have hez : z = fun j => ∑ p, c p * u p j := monotone_cut_expansion m z hz.2
  have hew : w = fun j => ∑ p, d p * u p j := monotone_cut_expansion m w hw.2
  have hcut (p q : Fin m) : normOne (u p) * normOne (u q) ≤
      4 * ((m + 1 : ℕ) : ℝ) * pairing (u p) (u q) := by
    rcases le_total p q with h | h
    · apply nested_cut_angle (by omega)
      exact Finset.Iic_subset_Iic.mpr h
    · have he := nested_cut_angle (by omega : 0 < m + 1)
        (Finset.Iic q.castSucc) (Finset.Iic p.castSucc)
        (Finset.Iic_subset_Iic.mpr h)
      simpa [u, pairing, mul_comm] using he
  have hnz : 0 ≤ normOne z := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hnw : 0 ≤ normOne w := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hcz : normOne z ≤ ∑ p, c p * normOne (u p) :=
    hez ▸ normOne_sum_le c u hc
  have hdw : normOne w ≤ ∑ p, d p * normOne (u p) :=
    hew ▸ normOne_sum_le d u hd
  have hprod : normOne z * normOne w ≤
      4 * ((m + 1 : ℕ) : ℝ) * pairing z w := by
    calc
      _ ≤ (∑ p, c p * normOne (u p)) * (∑ q, d q * normOne (u q)) :=
        mul_le_mul hcz hdw hnw (hnz.trans hcz)
      _ = ∑ p, ∑ q, c p * d q * (normOne (u p) * normOne (u q)) := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]; congr 1; funext p; congr 1; funext q; ring
      _ ≤ ∑ p, ∑ q, c p * d q * (4 * ((m + 1 : ℕ) : ℝ) * pairing (u p) (u q)) := by
        apply Finset.sum_le_sum
        intro p _
        apply Finset.sum_le_sum
        intro q _
        exact mul_le_mul_of_nonneg_left (hcut p q) (mul_nonneg (hc p) (hd q))
      _ = 4 * ((m + 1 : ℕ) : ℝ) * pairing z w := by
        have hpair : pairing z w = ∑ p, ∑ q, c p * d q * pairing (u p) (u q) := by
          simpa only [← hez, ← hew] using pairing_sum_smul c d u u
        simp only [hpair, Finset.mul_sum, mul_left_comm, mul_assoc]
  have hpos : (0 : ℝ) < 4 * ((m + 1 : ℕ) : ℝ) := by positivity
  calc
    _ = normOne z * normOne w / (4 * ((m + 1 : ℕ) : ℝ)) := by ring
    _ ≤ pairing z w := (div_le_iff₀ hpos).mpr (by nlinarith [hprod])

/-!
## Path preparation: matrix expansion in mixed differences

Turn adjacent mixed differences into coefficients of products of two-block averages and bound their total mass.
-/

private theorem twoBlock_entry {n : ℕ} (hn : 0 < n) (S : Finset (Fin n))
    (hs : 0 < S.card) (ht : S.card < n) (i j : Fin n) :
    twoBlockMatrix S i j = 1 / (n : ℝ) +
      cutVector S i * cutVector S j / ((S.card : ℝ) * ((n : ℝ) - S.card) / n) := by
  simpa only [Fintype.card_fin] using twoBlock_entry_general S hs (by simpa using ht) i j

private theorem twoBlock_product_entry {n : ℕ} (hn : 0 < n)
    (S T : Finset (Fin n)) (hs : 0 < S.card) (hsn : S.card < n)
    (ht : 0 < T.card) (htn : T.card < n) (i j : Fin n) :
    (twoBlockMatrix S * twoBlockMatrix T) i j = 1 / (n : ℝ) +
      (pairing (cutVector S) (cutVector T) /
        (((S.card : ℝ) * ((n : ℝ) - S.card) / n) *
          ((T.card : ℝ) * ((n : ℝ) - T.card) / n))) * cutVector S i * cutVector T j := by
  letI : NeZero n := ⟨hn.ne'⟩
  have block (U : Finset (Fin n)) (hU : 0 < U.card) (hUn : U.card < n) (i j : Fin n) :
      twoBlockMatrix U i j = 1 / (Fintype.card (Fin n) : ℝ) +
        (((U.card : ℝ) * ((n : ℝ) - U.card) / n)⁻¹) * cutVector U i * cutVector U j := by
    simpa only [Fintype.card_fin, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      using twoBlock_entry hn U hU hUn i j
  simpa only [Fintype.card_fin, div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]
    using rank_product_entry _ _ S S T T _ _ (block S hs hsn) (block T ht htn) i j

/-- Expand a zero-row-sum, zero-column-sum matrix in prefix cuts using its adjacent mixed differences. -/
private theorem mixed_cut_expansion (m : ℕ) (M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hM : M ∈ doublyStochastic ℝ (Fin (m + 1))) (i j : Fin (m + 1)) :
    M i j - 1 / ((m + 1 : ℕ) : ℝ) =
      ∑ p : Fin m, ∑ q : Fin m, mixedDifferences M p q *
        cutVector (Finset.Iic p.castSucc) i * cutVector (Finset.Iic q.castSucc) j := by
  have hnR : (((m + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hcol (j : Fin (m + 1)) : mass (fun i => M i j - 1 / ((m + 1 : ℕ) : ℝ)) = 0 := by
    simp only [mass, Finset.sum_sub_distrib, sum_col_of_mem_doublyStochastic hM,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  have hrow (p : Fin m) : mass (fun j => M p.castSucc j - M p.succ j) = 0 := by
    simp only [mass, Finset.sum_sub_distrib, sum_row_of_mem_doublyStochastic hM, sub_self]
  have he := congrFun (monotone_cut_expansion m _ (hcol j)) i
  simp only [sub_sub_sub_cancel_right] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro p _
  have hp := congrFun (monotone_cut_expansion m _ (hrow p)) j
  rw [hp, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q _
  change ((M p.castSucc q.castSucc - M p.succ q.castSucc -
    (M p.castSucc q.succ - M p.succ q.succ)) * _ ) * _ =
    (M p.castSucc q.castSucc - M p.succ q.castSucc -
      M p.castSucc q.succ + M p.succ q.succ) * _ * _
  ring

private theorem nested_twoBlock_factor {n : ℕ} (hn : 0 < n)
    (S T : Finset (Fin n)) (hs : 0 < S.card) (hsn : S.card < n)
    (ht : 0 < T.card) (htn : T.card < n) (hst : S ⊆ T) :
    ∃ c : ℝ, 0 ≤ c ∧ c ≤ n ∧ ∀ i j,
      c * ((twoBlockMatrix S * twoBlockMatrix T) i j - 1 / (n : ℝ)) =
        cutVector S i * cutVector T j := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsR : (0 : ℝ) < S.card := by exact_mod_cast hs
  have htR : (0 : ℝ) < T.card := by exact_mod_cast ht
  have hsR' : (S.card : ℝ) < n := by exact_mod_cast hsn
  have htR' : (T.card : ℝ) < n := by exact_mod_cast htn
  refine ⟨(T.card : ℝ) * ((n : ℝ) - S.card) / n, by positivity, ?_, ?_⟩
  · apply (div_le_iff₀ hnR).mpr
    nlinarith
  · intro i j
    rw [twoBlock_product_entry hn S T hs hsn ht htn,
      cut_pairing hn, Finset.inter_eq_left.mpr hst]
    field_simp [hnR.ne', hsR.ne', htR.ne', (sub_pos.mpr hsR').ne', (sub_pos.mpr htR').ne']
    <;> ring

private theorem prefix_twoBlock_factor (m : ℕ) (p q : Fin m) :
    ∃ c : ℝ, 0 ≤ c ∧ c ≤ (m + 1 : ℕ) ∧ ∀ i j,
      c * ((twoBlockMatrix (Finset.Iic p.castSucc) *
        twoBlockMatrix (Finset.Iic q.castSucc)) i j - 1 / ((m + 1 : ℕ) : ℝ)) =
        cutVector (Finset.Iic p.castSucc) i * cutVector (Finset.Iic q.castSucc) j := by
  have hs (r : Fin m) : 0 < (Finset.Iic r.castSucc).card := by simp [Fin.card_Iic]
  have ht (r : Fin m) : (Finset.Iic r.castSucc).card < m + 1 := by
    simp only [Fin.card_Iic, Fin.val_castSucc]
    omega
  rcases le_total p q with h | h
  · exact nested_twoBlock_factor (by omega) _ _ (hs p) (ht p) (hs q) (ht q)
      (Finset.Iic_subset_Iic.mpr h)
  · obtain ⟨c, hc0, hcn, hc⟩ := nested_twoBlock_factor (by omega : 0 < m + 1)
      _ _ (hs q) (ht q) (hs p) (ht p) (Finset.Iic_subset_Iic.mpr h)
    refine ⟨c, hc0, hcn, fun i j => ?_⟩
    have heq : (twoBlockMatrix (Finset.Iic p.castSucc) *
        twoBlockMatrix (Finset.Iic q.castSucc)) i j =
        (twoBlockMatrix (Finset.Iic q.castSucc) * twoBlockMatrix (Finset.Iic p.castSucc)) j i := by
      simp only [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro k _
      rw [twoBlock_entry (by omega) _ (hs p) (ht p),
        twoBlock_entry (by omega) _ (hs q) (ht q),
        twoBlock_entry (by omega) _ (hs q) (ht q),
        twoBlock_entry (by omega) _ (hs p) (ht p)]
      ring
    rw [heq, hc, mul_comm]

private theorem sum_adjacent_sub {m : ℕ} (f : Fin (m + 1) → ℝ) :
    (∑ i : Fin m, (f i.castSucc - f i.succ)) = f 0 - f (Fin.last m) := by
  rw [Finset.sum_sub_distrib]
  have h₁ := Fin.sum_univ_castSucc f
  have h₂ := Fin.sum_univ_succ f
  linarith

private theorem mixed_sum_bound (m : ℕ) (M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) :
    (∑ p : Fin m, ∑ q : Fin m, mixedDifferences M p q) ≤
      4 * maxEntryNorm (M - consensusMatrix) := by
  have heq : (∑ p : Fin m, ∑ q : Fin m, mixedDifferences M p q) =
      M 0 0 - M 0 (Fin.last m) - M (Fin.last m) 0 + M (Fin.last m) (Fin.last m) := by
    have hdiff (p q : Fin m) : mixedDifferences M p q =
        (M p.castSucc q.castSucc - M p.succ q.castSucc) -
          (M p.castSucc q.succ - M p.succ q.succ) := by
      change M p.castSucc q.castSucc - M p.succ q.castSucc -
        M p.castSucc q.succ + M p.succ q.succ = _
      ring
    have hinner (p : Fin m) : (∑ q : Fin m, mixedDifferences M p q) =
        (M p.castSucc 0 - M p.succ 0) -
          (M p.castSucc (Fin.last m) - M p.succ (Fin.last m)) := by
      simp_rw [hdiff]
      exact sum_adjacent_sub (fun q => M p.castSucc q - M p.succ q)
    simp_rw [hinner]
    rw [Finset.sum_sub_distrib, sum_adjacent_sub (fun p => M p 0),
      sum_adjacent_sub (fun p => M p (Fin.last m))]
    ring
  have hentry (i j : Fin (m + 1)) :
      |M i j - 1 / ((m + 1 : ℕ) : ℝ)| ≤ maxEntryNorm (M - consensusMatrix) := by
    unfold maxEntryNorm
    simp only [Matrix.sub_apply, consensusMatrix, Fintype.card_fin]
    exact (Real.norm_eq_abs _).symm ▸ norm_le_pi_norm
      (fun p : Fin (m + 1) × Fin (m + 1) => M p.1 p.2 - 1 / ((m + 1 : ℕ) : ℝ)) (i, j)
  rw [heq]
  linarith [(abs_le.mp (hentry 0 0)).2, (abs_le.mp (hentry 0 (Fin.last m))).1,
    (abs_le.mp (hentry (Fin.last m) 0)).1, (abs_le.mp (hentry (Fin.last m) (Fin.last m))).2]

private theorem prefix_cut_legal (m : ℕ) (p : Fin m) :
    IsLegalMove (SimpleGraph.pathGraph (m + 1)) (Finset.Iic p.castSucc) ∧
      IsLegalMove (SimpleGraph.pathGraph (m + 1)) (Finset.univ \ Finset.Iic p.castSucc) := by
  constructor
  · have heq : Finset.Icc (0 : Fin (m + 1)) p.castSucc = Finset.Iic p.castSucc := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_Iic]
      exact and_iff_right (Fin.zero_le i)
    simpa only [pathInterval, heq] using pathInterval_legal (0 : Fin (m + 1)) p.castSucc (Fin.zero_le _)
  · have heq : Finset.univ \ Finset.Iic p.castSucc = Finset.Icc p.succ (Fin.last m) := by
      ext i
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_Iic, Finset.mem_Icc,
        Fin.le_def, Fin.val_castSucc, Fin.val_succ, Fin.val_last]
      omega
    rw [heq]
    exact pathInterval_legal p.succ (Fin.last m) (Fin.le_last _)

private theorem twoBlock_product_mem_path_four (m : ℕ) (p q : Fin m) :
    twoBlockMatrix (Finset.Iic p.castSucc) * twoBlockMatrix (Finset.Iic q.castSucc) ∈
      operatorPolytope (SimpleGraph.pathGraph (m + 1)) 4 := by
  let S := Finset.Iic p.castSucc
  let T := Finset.Iic q.castSucc
  have htwo (A : Finset (Fin (m + 1))) : strategyMatrix [Finset.univ \ A, A] = twoBlockMatrix A := by
    rw [show [Finset.univ \ A, A] = [Finset.univ \ A] ++ [A] from rfl, strategyMatrix_append]
    rfl
  have heq : strategyMatrix [Finset.univ \ T, T, Finset.univ \ S, S] =
      twoBlockMatrix S * twoBlockMatrix T := by
    rw [show [Finset.univ \ T, T, Finset.univ \ S, S] =
      [Finset.univ \ T, T] ++ [Finset.univ \ S, S] from rfl, strategyMatrix_append,
      htwo, htwo]
  rw [← heq]
  apply strategyMatrix_mem_polytope _ _ _ (by simp)
  intro A hA
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
  rcases hA with rfl | rfl | rfl | rfl
  · exact (prefix_cut_legal m q).2
  · exact (prefix_cut_legal m q).1
  · exact (prefix_cut_legal m p).2
  · exact (prefix_cut_legal m p).1

private theorem consensus_mem_path_four (m : ℕ) :
    (consensusMatrix : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∈
      operatorPolytope (SimpleGraph.pathGraph (m + 1)) 4 := by
  have heq : strategyMatrix ([Finset.univ] : Strategy (Fin (m + 1))) = consensusMatrix := by
    ext i j
    simp [strategyMatrix, run, average, mean, pointMass, consensusMatrix]
  rw [← heq]
  apply strategyMatrix_mem_polytope _ _ _ (by simp)
  intro S hS
  simp only [List.mem_singleton] at hS
  subst S
  have heq : Finset.Icc (0 : Fin (m + 1)) (Fin.last m) = Finset.univ := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_univ, iff_true]
    exact ⟨Fin.zero_le i, Fin.le_last i⟩
  simpa only [pathInterval, heq] using
    pathInterval_legal (0 : Fin (m + 1)) (Fin.last m) (Fin.zero_le _)

/-!
## Lemma 5.1: exact four-step path decomposition

Combine nonnegative mixed differences with the coefficient bound and place unused weight at consensus.
-/

/-- Lemma 5.1: nonnegative mixed differences supply convex coefficients for short
path operators; put the remaining coefficient on the global consensus average. -/
theorem path_cone_decomposition (n : ℕ) (hn : 2 ≤ n)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n))
    (hdiff : ∀ i j, 0 ≤ mixedDifferences M i j)
    (hnear : maxEntryNorm (M - consensusMatrix) ≤ 1 / (4 * (n : ℝ))) :
    M ∈ operatorPolytope (SimpleGraph.pathGraph n) 4 := by
  classical
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hnR : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  choose c hc0 hcn hceq using prefix_twoBlock_factor m
  let E (p : Fin m × Fin m) :=
    twoBlockMatrix (Finset.Iic p.1.castSucc) * twoBlockMatrix (Finset.Iic p.2.castSucc)
  let coeff (p : Fin m × Fin m) : ℝ := mixedDifferences M p.1 p.2 * c p.1 p.2
  let Λ : ℝ := ∑ p, coeff p
  have hcoeff0 (p : Fin m × Fin m) : 0 ≤ coeff p := mul_nonneg (hdiff _ _) (hc0 _ _)
  have hΛ : Λ ≤ 1 := by
    calc
      Λ ≤ ((m + 1 : ℕ) : ℝ) * (∑ p : Fin m, ∑ q : Fin m, mixedDifferences M p q) := by
        simp only [Λ, coeff, Fintype.sum_prod_type, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro p _
        apply Finset.sum_le_sum
        intro q _
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hcn p q) (hdiff p q)
      _ ≤ ((m + 1 : ℕ) : ℝ) * (4 * maxEntryNorm (M - consensusMatrix)) :=
        mul_le_mul_of_nonneg_left (mixed_sum_bound m M) hnR.le
      _ ≤ ((m + 1 : ℕ) : ℝ) * (4 * (1 / (4 * ((m + 1 : ℕ) : ℝ)))) := by
        gcongr
      _ = 1 := by field_simp
  apply convex_decomposition_of_deviations _ (convex_convexHull ℝ _) consensusMatrix M
    (consensus_mem_path_four m) coeff E hcoeff0 hΛ
    (fun p => twoBlock_product_mem_path_four m p.1 p.2)
  intro i j
  simp only [coeff, E, Fintype.sum_prod_type, consensusMatrix, Fintype.card_fin]
  calc
    _ = ∑ p : Fin m, ∑ q : Fin m, mixedDifferences M p q *
        cutVector (Finset.Iic p.castSucc) i * cutVector (Finset.Iic q.castSucc) j := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      rw [mul_assoc, hceq]
      ring
    _ = _ := (mixed_cut_expansion m M hM i j).symm

/-!
## Preparation for two factors: stability near the monotone cone

Control pairing errors, then apply total-nonnegative row and column ratio estimates.
-/

private theorem normOne_nonneg {n : ℕ} (z : State (Fin n)) : 0 ≤ normOne z :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

private theorem normOne_sub_triangle {n : ℕ} (d z : State (Fin n)) :
    normOne d ≤ normOne (d - z) + normOne z := by
  rw [normOne, normOne, normOne, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  simpa only [Pi.sub_apply, sub_add_cancel] using abs_add_le (d j - z j) (z j)

private theorem abs_pairing_le {n : ℕ} (d e : State (Fin n)) :
    |pairing d e| ≤ normOne d * normOne e := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [normOne, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left
    (Finset.single_le_sum (fun j _ => abs_nonneg (e j)) hi) (abs_nonneg _)

/-- If two zero-sum differences are sufficiently close to the monotone cone, the
paper's error bound still guarantees their pairing is nonnegative. -/
private theorem near_cone_pairing_nonneg {n : ℕ} (hn : 1 ≤ n)
    (d e z w : State (Fin n)) (hz : z ∈ centeredMonotoneCone n)
    (hw : w ∈ centeredMonotoneCone n)
    (hd : normOne (d - z) ≤ 1 / (16 * (n : ℝ)) * normOne d)
    (he : normOne (e - w) ≤ 1 / (16 * (n : ℝ)) * normOne e) :
    0 ≤ pairing d e := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hγ : 1 / (16 * (n : ℝ)) ≤ (1 / 16 : ℝ) := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hdn := normOne_nonneg d
  have hen := normOne_nonneg e
  have hzn := normOne_nonneg z
  have hwn := normOne_nonneg w
  have hdsmall : normOne (d - z) ≤ 1 / 16 * normOne d :=
    hd.trans (mul_le_mul_of_nonneg_right hγ hdn)
  have hesmall : normOne (e - w) ≤ 1 / 16 * normOne e :=
    he.trans (mul_le_mul_of_nonneg_right hγ hen)
  have hzlo : 15 / 16 * normOne d ≤ normOne z := by
    linarith [normOne_sub_triangle d z]
  have hwlo : 15 / 16 * normOne e ≤ normOne w := by
    linarith [normOne_sub_triangle e w]
  have hzhi : normOne z ≤ 2 * normOne d := by
    have h := normOne_sub_triangle z d
    have hs : normOne (z - d) = normOne (d - z) := by
      simp only [normOne, Pi.sub_apply, abs_sub_comm]
    rw [hs] at h
    linarith
  have hprod : 225 / 256 * (normOne d * normOne e) ≤ normOne z * normOne w := by
    nlinarith [mul_le_mul hzlo hwlo (by positivity) hzn]
  have hangle := monotone_cone_angle n hn z w hz hw
  have hangle' : normOne z * normOne w ≤ 4 * (n : ℝ) * pairing z w := by
    rw [mul_comm (4 * (n : ℝ))]
    apply (div_le_iff₀ (by positivity : 0 < 4 * (n : ℝ))).mp
    calc
      normOne z * normOne w / (4 * (n : ℝ)) =
          1 / (4 * (n : ℝ)) * normOne z * normOne w := by ring
      _ ≤ pairing z w := hangle
  have hde : 16 * (n : ℝ) * normOne (d - z) ≤ normOne d := by
    rw [one_div_mul_eq_div] at hd
    apply (le_div_iff₀ (by positivity : 0 < 16 * (n : ℝ))).mp at hd
    nlinarith [hd]
  have hew : 16 * (n : ℝ) * normOne (e - w) ≤ normOne e := by
    rw [one_div_mul_eq_div] at he
    apply (le_div_iff₀ (by positivity : 0 < 16 * (n : ℝ))).mp at he
    nlinarith [he]
  have herr1 : 4 * (n : ℝ) * (normOne (d - z) * normOne e) ≤
      1 / 4 * (normOne d * normOne e) := by
    nlinarith [mul_le_mul_of_nonneg_right hde hen]
  have herr2 : 4 * (n : ℝ) * (normOne z * normOne (e - w)) ≤
      1 / 2 * (normOne d * normOne e) := by
    have h1 := mul_le_mul_of_nonneg_left hew hzn
    have h2 := mul_le_mul_of_nonneg_right hzhi hen
    nlinarith
  have hid : pairing d e - pairing z w = pairing (d - z) e + pairing z (e - w) := by
    simp only [pairing, Pi.sub_apply, sub_mul, mul_sub, Finset.sum_sub_distrib]
    ring
  have herr : pairing z w ≤ pairing d e +
      normOne (d - z) * normOne e + normOne z * normOne (e - w) := by
    have h1 := (abs_le.mp (abs_pairing_le (d - z) e)).1
    have h2 := (abs_le.mp (abs_pairing_le z (e - w))).1
    linarith
  have h := mul_le_mul_of_nonneg_left herr (by positivity : 0 ≤ 4 * (n : ℝ))
  have hnon := mul_nonneg hdn hen
  nlinarith

private theorem tnn_row_ratio {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : TotallyNonnegative M) (hpos : ∀ i j, 0 < M i j)
    {i j : Fin n} (hij : i < j) : Antitone (fun k => M i k / M j k) := by
  intro k l hkl
  rcases hkl.eq_or_lt with rfl | hkl
  · rfl
  · have hr : StrictMono ![i, j] := by
      rw [Fin.strictMono_iff_lt_succ]
      intro p
      fin_cases p
      simpa using hij
    have hc : StrictMono ![k, l] := by
      rw [Fin.strictMono_iff_lt_succ]
      intro p
      fin_cases p
      simpa using hkl
    have h := hM 2 ![i, j] ![k, l] hr hc
    simp only [Matrix.det_fin_two, Matrix.submatrix_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one] at h
    apply (div_le_div_iff₀ (hpos j l) (hpos j k)).mpr
    nlinarith

private theorem tnn_transpose {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : TotallyNonnegative M) : TotallyNonnegative M.transpose := by
  intro k r c hr hc
  change 0 ≤ Matrix.det (M.submatrix c r).transpose
  rw [Matrix.det_transpose]
  exact hM k c r hc hr

/-!
## Proposition 5.5: replace two mixed path factors

The product has the mixed-difference signs required for the four-step decomposition.
-/

/-- Proposition 5.5: two sufficiently near-consensus totally nonnegative factors
have product in the four-step path hull; the factors need not themselves be strategy matrices. -/
theorem path_two_factor_decomposition (n : ℕ) (hn : 2 ≤ n)
    (P Q : Matrix (Fin n) (Fin n) ℝ)
    (hP : P ∈ doublyStochastic ℝ (Fin n)) (hQ : Q ∈ doublyStochastic ℝ (Fin n))
    (htP : TotallyNonnegative P) (htQ : TotallyNonnegative Q)
    (hp : maxEntryNorm (P - consensusMatrix) ≤ 1 / (64 * (n : ℝ) ^ 2))
    (hq : maxEntryNorm (Q - consensusMatrix) ≤ 1 / (64 * (n : ℝ) ^ 2)) :
    (∀ i j, 0 ≤ mixedDifferences (P * Q) i j) ∧
    P * Q ∈ operatorPolytope (SimpleGraph.pathGraph n) 4 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  let η : ℝ := 1 / (64 * (n : ℝ))
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hη1 : η < 1 := by
    dsimp [η]
    apply (div_lt_iff₀ (by positivity)).mpr
    linarith
  have hcoeff : 2 * η / (1 - η) ≤ 1 / (16 * (n : ℝ)) := by
    have hd : 0 < 64 * (n : ℝ) - 1 := by linarith
    have heq : 2 * η / (1 - η) = 2 / (64 * (n : ℝ) - 1) := by
      dsimp [η]
      field_simp
    rw [heq]
    apply (div_le_div_iff₀ hd (by positivity)).mpr
    linarith
  have entries (M : Matrix (Fin n) (Fin n) ℝ)
      (hm : maxEntryNorm (M - consensusMatrix) ≤ 1 / (64 * (n : ℝ) ^ 2)) :
      (∀ i j, 0 < M i j) ∧ ∀ i j, |(n : ℝ) * M i j - 1| ≤ η := by
    have hentry (i j : Fin n) : |M i j - 1 / (n : ℝ)| ≤ 1 / (64 * (n : ℝ) ^ 2) := by
      have h := (norm_le_pi_norm (fun p : Fin n × Fin n =>
        (M - consensusMatrix : Matrix (Fin n) (Fin n) ℝ) p.1 p.2) (i, j)).trans hm
      simpa only [Real.norm_eq_abs, Matrix.sub_apply, consensusMatrix, Fintype.card_fin] using h
    constructor
    · intro i j
      have hsmall : 1 / (64 * (n : ℝ) ^ 2) < 1 / (n : ℝ) := by
        apply (div_lt_div_iff₀ (by positivity) hnpos).mpr
        nlinarith
      have h := (abs_le.mp (hentry i j)).1
      linarith
    · intro i j
      calc
        |(n : ℝ) * M i j - 1| = |(n : ℝ) * (M i j - 1 / (n : ℝ))| := by
          congr 1
          field_simp
        _ = (n : ℝ) * |M i j - 1 / (n : ℝ)| := by rw [abs_mul, abs_of_pos hnpos]
        _ ≤ (n : ℝ) * (1 / (64 * (n : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (hentry i j) hnpos.le
        _ = η := by dsimp [η]; field_simp
  obtain ⟨hp0, hpη⟩ := entries P hp
  obtain ⟨hq0, hqη⟩ := entries Q hq
  have hdiff (i j : Fin (n - 1)) : 0 ≤ mixedDifferences (P * Q) i j := by
    let a : Fin n := ⟨i.val, by omega⟩
    let b : Fin n := ⟨i.val + 1, by omega⟩
    let c : Fin n := ⟨j.val, by omega⟩
    let d : Fin n := ⟨j.val + 1, by omega⟩
    have hab : a < b := by simp [a, b, Fin.lt_def]
    have hcd : c < d := by simp [c, d, Fin.lt_def]
    obtain ⟨z, hz, hdz⟩ := ratio_near_monotone n (by omega) (P a) (P b)
      (hp0 a) (hp0 b) (sum_row_of_mem_doublyStochastic hP a)
      (sum_row_of_mem_doublyStochastic hP b) (tnn_row_ratio P htP hp0 hab)
      η hη hη1 (hpη b)
    obtain ⟨w, hw, hew⟩ := ratio_near_monotone n (by omega) (Q.transpose c) (Q.transpose d)
      (fun k => hq0 k c) (fun k => hq0 k d) (sum_col_of_mem_doublyStochastic hQ c)
      (sum_col_of_mem_doublyStochastic hQ d)
      (tnn_row_ratio Q.transpose (tnn_transpose Q htQ) (fun i j => hq0 j i) hcd)
      η hη hη1 (fun k => hqη k d)
    have h := near_cone_pairing_nonneg (by omega : 1 ≤ n)
      (P a - P b) (Q.transpose c - Q.transpose d) z w hz hw
      (hdz.trans (mul_le_mul_of_nonneg_right hcoeff (normOne_nonneg _)))
      (hew.trans (mul_le_mul_of_nonneg_right hcoeff (normOne_nonneg _)))
    convert h using 1
    change (P * Q) a c - (P * Q) b c - (P * Q) a d + (P * Q) b d = _
    simp only [pairing, Matrix.mul_apply, Pi.sub_apply, Matrix.transpose_apply,
      sub_mul, mul_sub, Finset.sum_sub_distrib]
    ring
  refine ⟨hdiff, path_cone_decomposition n hn (P * Q)
    ((doublyStochastic ℝ (Fin n)).mul_mem hP hQ) hdiff ?_⟩
  apply (maxEntryNorm_mul_consensus_le P Q hP).trans (hq.trans ?_)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

/-!
## Proposition 2.4: the common local replacement theorem

Combine the path and nonpath arguments and transport path coordinates through a graph isomorphism.
-/

/-- Proposition 2.4: the product of two sufficiently mixed strategy blocks has an
exact convex decomposition into strategies of length at most six.
The path branch retains the stronger four-step conclusion. -/
theorem local_replacement (G : SimpleGraph V) (hG : G.Connected)
    (hn : 3 ≤ Fintype.card V) (P Q : Matrix V V ℝ)
    (hP : P ∈ strategyOperators G) (hQ : Q ∈ strategyOperators G)
    (hp : maxEntryNorm (P - consensusMatrix) ≤ localRadius (Fintype.card V))
    (hq : maxEntryNorm (Q - consensusMatrix) ≤ localRadius (Fintype.card V)) :
    Q * P ∈ operatorPolytope G 6 ∧
      (IsPathGraph G → Q * P ∈ operatorPolytope G 4) := by
  classical
  have ds (M : Matrix V V ℝ) (hM : M ∈ strategyOperators G) :
      M ∈ doublyStochastic ℝ V := by
    obtain ⟨σ, _, rfl⟩ := hM
    exact strategyMatrix_doublyStochastic σ
  have hpath (e : G ≃g SimpleGraph.pathGraph (Fintype.card V)) :
      Q * P ∈ operatorPolytope G 4 := by
    let f := Matrix.reindexLinearEquiv ℝ ℝ e.toEquiv e.toEquiv
    have ht (M : Matrix V V ℝ) (hM : M ∈ strategyOperators G) :
        TotallyNonnegative (f M) := by
      obtain ⟨σ, hσ, rfl⟩ := hM
      change TotallyNonnegative (Matrix.reindex e.toEquiv e.toEquiv (strategyMatrix σ))
      rw [← strategyMatrix_reindex]
      exact path_strategy_totallyNonnegative _ _ (hσ.map_iso e)
    have hnR : (3 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
    have hnear (M : Matrix V V ℝ)
        (hm : maxEntryNorm (M - consensusMatrix) ≤ localRadius (Fintype.card V)) :
        maxEntryNorm (f M - consensusMatrix) ≤
          1 / (64 * (Fintype.card V : ℝ) ^ 2) := by
      have hj : f consensusMatrix = consensusMatrix := consensusMatrix_reindex e.toEquiv
      rw [← hj, ← map_sub]
      change maxEntryNorm (Matrix.reindex e.toEquiv e.toEquiv (M - consensusMatrix)) ≤ _
      rw [maxEntryNorm_reindex]
      apply hm.trans
      unfold localRadius
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have hn3 : (16 : ℝ) ≤ (Fintype.card V : ℝ) ^ 3 := by
        have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hnR 3
        norm_num at h
        linarith
      nlinarith [mul_nonneg (sq_nonneg (Fintype.card V : ℝ)) (sub_nonneg.mpr hn3)]
    have hfour := (path_two_factor_decomposition (Fintype.card V) (by omega)
      (f Q) (f P) (reindex_mem_doublyStochastic (ds Q hQ))
      (reindex_mem_doublyStochastic (ds P hP)) (ht Q hQ) (ht P hP)
      (hnear Q hq) (hnear P hp)).2
    have hmul : f Q * f P = f (Q * P) :=
      Matrix.reindexLinearEquiv_mul ℝ ℝ e.toEquiv e.toEquiv e.toEquiv Q P
    rw [hmul] at hfour
    have hback := operatorPolytope_map_iso e.symm 4 hfour
    have heq : Matrix.reindex e.symm.toEquiv e.symm.toEquiv (f (Q * P)) = Q * P := by
      ext i j
      change (Q * P) (e.symm (e i)) (e.symm (e j)) = (Q * P) i j
      simp
    rwa [heq] at hback
  by_cases h : IsPathGraph G
  · obtain ⟨e⟩ := h
    exact ⟨operatorPolytope_mono G (by decide : 4 ≤ 6) (hpath e), fun _ => hpath e⟩
  · refine ⟨nonpath_local_decomposition G hG h (Q * P) ?_ ?_, fun hp => (h hp).elim⟩
    · exact (mem_doublyStochastic_iff_sum.mp
        ((doublyStochastic ℝ V).mul_mem (ds Q hQ) (ds P hP))).2
    · exact (maxEntryNorm_mul_consensus_le Q P (ds Q hQ)).trans hp

end WaterTransport.Paper3
