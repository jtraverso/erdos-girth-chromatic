/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import FractionalLib.Basic
public import Mycielski.Basic

/-!
# The fractional chromatic number of Mycielski graphs

Larsen, Propp and Ullman, *The fractional chromatic number of Mycielski's graphs*,
J. Graph Theory 19 (1995) 411–416: for every finite graph `G` with at least one vertex,
`χ_f(M(G)) = χ_f(G) + 1/χ_f(G)`.

* Upper bound: a fractional colouring `x` of `G` of weight `t` gives the fractional colouring of
  `M(G)` with weight `(t−1)/t · x(I)` on `I ∪ I'`, `x(I)/t` on `I ∪ {w}` and `1/t` on the shadow
  layer, of total weight `t + 1/t`.
* Lower bound: an optimal fractional clique `g` of `G` (strong duality) gives the fractional
  clique `(1 − 1/a) g` on the original layer, `g/a` on the shadows and `1/a` on the apex, of
  total weight `a + 1/a`, `a = χ_f(G)`. Independence of the shadow part uses the restriction of
  `G` to the vertices outside the closed neighbourhood of the original part (weak duality).
-/

@[expose] public section

open Finset hiding shadow
open Mycielski

namespace FractionalColouring

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-! ### Splitting sums over the Mycielski vertex type -/

/-- A sum over a set of Mycielski vertices, split into apex, original and shadow parts. -/
theorem sum_split (S : Finset (Vertex V)) (h : Vertex V → ℝ) :
    ∑ u ∈ S, h u = (if none ∈ S then h none else 0) +
      ∑ v ∈ univ.filter (fun v => original v ∈ S), h (original v) +
      ∑ v ∈ univ.filter (fun v => shadow v ∈ S), h (shadow v) := by
  have hS : ∑ u ∈ S, h u = ∑ u, if u ∈ S then h u else 0 := by
    rw [← Finset.sum_filter]; congr 1; ext u; simp
  rw [hS, Fintype.sum_option, Fintype.sum_prod_type, Finset.sum_filter, Finset.sum_filter]
  simp only [Fintype.sum_bool, Finset.sum_add_distrib, original, shadow]
  exact (add_assoc (G := ℝ) _ _ _).symm.trans (add_right_comm _ _ _)

/-! ### Independent sets of the Mycielski graph -/

/-- The set `I ∪ I'` for a vertex set `I` of `G`. -/
def lift (s : Finset V) : Finset (Vertex V) := s.image original ∪ s.image shadow

/-- The set `I ∪ {w}` for a vertex set `I` of `G`. -/
def liftApex (s : Finset V) : Finset (Vertex V) := insert none (s.image original)

/-- The shadow layer. -/
def shadows : Finset (Vertex V) := univ.image shadow

omit [Fintype V] in
@[simp] theorem original_mem_lift {s : Finset V} {v : V} : original v ∈ lift s ↔ v ∈ s := by
  simp [lift, original, shadow]

omit [Fintype V] in
@[simp] theorem shadow_mem_lift {s : Finset V} {v : V} : shadow v ∈ lift s ↔ v ∈ s := by
  simp [lift, original, shadow]

omit [Fintype V] in
@[simp] theorem none_not_mem_lift {s : Finset V} : none ∉ lift s := by
  simp [lift, original, shadow]

omit [Fintype V] in
@[simp] theorem original_mem_liftApex {s : Finset V} {v : V} :
    original v ∈ liftApex s ↔ v ∈ s := by
  simp [liftApex, original]

omit [Fintype V] in
@[simp] theorem shadow_not_mem_liftApex {s : Finset V} {v : V} : shadow v ∉ liftApex s := by
  simp [liftApex, original, shadow]

omit [Fintype V] in
@[simp] theorem none_mem_liftApex {s : Finset V} : none ∈ liftApex s := by
  simp [liftApex]

@[simp] theorem original_not_mem_shadows {v : V} : original v ∉ (shadows : Finset (Vertex V)) := by
  simp [shadows, original, shadow]

@[simp] theorem shadow_mem_shadows {v : V} : shadow v ∈ (shadows : Finset (Vertex V)) := by
  simp [shadows]

@[simp] theorem none_not_mem_shadows : none ∉ (shadows : Finset (Vertex V)) := by
  simp [shadows, shadow]

variable {G}

theorem isIndepSet_lift {s : Finset V} (hs : G.IsIndepSet (s : Set V)) :
    (graph G).IsIndepSet ((lift s : Finset (Vertex V)) : Set (Vertex V)) := by
  intro u hu u' hu' huu'
  simp only [lift, coe_union, coe_image, Set.mem_union, Set.mem_image, mem_coe] at hu hu'
  rcases hu with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩ <;> rcases hu' with ⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩
  · exact hs hv hw (fun h => huu' (by rw [h]))
  · simp only [original_adj_shadow]
    by_cases hvw : v = w
    · subst hvw; exact G.irrefl
    · exact hs hv hw hvw
  · simp only [shadow_adj_original]
    by_cases hvw : v = w
    · subst hvw; exact G.irrefl
    · exact hs hv hw hvw
  · exact not_shadow_adj_shadow G v w

theorem isIndepSet_liftApex {s : Finset V} (hs : G.IsIndepSet (s : Set V)) :
    (graph G).IsIndepSet ((liftApex s : Finset (Vertex V)) : Set (Vertex V)) := by
  intro u hu u' hu' huu'
  simp only [liftApex, coe_insert, coe_image, Set.mem_insert_iff, Set.mem_image, mem_coe] at hu hu'
  rcases hu with rfl | ⟨v, hv, rfl⟩ <;> rcases hu' with rfl | ⟨w, hw, rfl⟩
  · exact absurd rfl huu'
  · simp [graph, Mycielski.Adj, original]
  · simp [graph, Mycielski.Adj, original]
  · exact hs hv hw (fun h => huu' (by rw [h]))

theorem isIndepSet_shadows :
    (graph G).IsIndepSet ((shadows : Finset (Vertex V)) : Set (Vertex V)) := by
  intro u hu u' hu' _
  simp only [shadows, coe_image, coe_univ, Set.image_univ, Set.mem_range] at hu hu'
  obtain ⟨v, rfl⟩ := hu
  obtain ⟨w, rfl⟩ := hu'
  exact not_shadow_adj_shadow G v w

/-! ### Upper bound -/

/-- A sum of indicator weights over the sets containing `u`. -/
theorem sum_filter_ite_eq (u : Vertex V) (L : Finset (Vertex V)) (c : ℝ) :
    ∑ S ∈ univ.filter (fun S => u ∈ S), (if S = L then c else 0) = if u ∈ L then c else 0 := by
  rw [Finset.sum_ite_eq']
  simp

/-- The fractional colouring of `M(G)` built from a fractional colouring of `G` of weight `t`. -/
noncomputable def mycielskiColouring (x : Finset V → ℝ) (t : ℝ) : Finset (Vertex V) → ℝ :=
  fun S => ∑ s, ((if S = lift s then x s * ((t - 1) / t) else 0) +
    (if S = liftApex s then x s / t else 0)) + (if S = shadows then 1 / t else 0)

theorem mycielskiColouring_cover (x : Finset V → ℝ) (t : ℝ) (u : Vertex V) :
    ∑ S ∈ univ.filter (fun S => u ∈ S), mycielskiColouring x t S =
      ∑ s, ((if u ∈ lift s then x s * ((t - 1) / t) else 0) +
        (if u ∈ liftApex s then x s / t else 0)) + (if u ∈ shadows then 1 / t else 0) := by
  unfold mycielskiColouring
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  simp only [Finset.sum_add_distrib, sum_filter_ite_eq]

theorem mycielskiColouring_sum (x : Finset V → ℝ) (t : ℝ) :
    ∑ S, mycielskiColouring x t S = ∑ s, x s * ((t - 1) / t) + ∑ s, x s / t + 1 / t := by
  unfold mycielskiColouring
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem isFracColouring_mycielskiColouring {x : Finset V → ℝ} (hx : IsFracColouring G x)
    {t : ℝ} (ht : 1 ≤ t) (hxt : ∑ s, x s = t) :
    IsFracColouring (graph G) (mycielskiColouring x t) := by
  have ht0 : 0 < t := by linarith
  have hc : 0 ≤ (t - 1) / t := div_nonneg (by linarith) ht0.le
  refine ⟨fun S => ?_, fun S hS => ?_, fun u => ?_⟩
  · unfold mycielskiColouring
    have h1 : ∀ s, 0 ≤ (if S = lift s then x s * ((t - 1) / t) else 0) := fun s => by
      split_ifs
      exacts [mul_nonneg (hx.1 s) hc, le_rfl]
    have h2 : ∀ s, 0 ≤ (if S = liftApex s then x s / t else 0) := fun s => by
      split_ifs
      exacts [div_nonneg (hx.1 s) ht0.le, le_rfl]
    have h3 : 0 ≤ (if S = shadows then 1 / t else 0) := by
      split_ifs
      exacts [div_nonneg zero_le_one ht0.le, le_rfl]
    exact add_nonneg (Finset.sum_nonneg fun s _ => add_nonneg (h1 s) (h2 s)) h3
  · unfold mycielskiColouring
    have h3 : (if S = shadows then 1 / t else 0) = 0 := by
      rw [if_neg]; rintro rfl; exact hS isIndepSet_shadows
    rw [h3, add_zero]
    refine Finset.sum_eq_zero fun s _ => ?_
    have hxs : ¬ G.IsIndepSet (s : Set V) → x s = 0 := hx.2.1 s
    by_cases hs : G.IsIndepSet (s : Set V)
    · rw [if_neg (by rintro rfl; exact hS (isIndepSet_lift hs)),
        if_neg (by rintro rfl; exact hS (isIndepSet_liftApex hs))]
      simp
    · simp [hxs hs]
  · rw [mycielskiColouring_cover]
    rcases u with _ | ⟨v, _ | _⟩
    · -- the apex
      simp only [none_not_mem_lift, none_mem_liftApex, none_not_mem_shadows, if_false, if_true,
        zero_add, add_zero]
      rw [← Finset.sum_div, hxt, div_self ht0.ne']
    · -- an original vertex
      have h := hx.2.2 v
      simp only [show (some (v, false) : Vertex V) = original v from rfl, original_mem_lift,
        original_mem_liftApex, original_not_mem_shadows, if_false, add_zero]
      rw [Finset.sum_filter] at h
      calc (1 : ℝ) ≤ ∑ s, if v ∈ s then x s else 0 := h
        _ = ∑ s, ((if v ∈ s then x s * ((t - 1) / t) else 0) + if v ∈ s then x s / t else 0) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          split_ifs
          · field_simp; ring
          · simp
    · -- a shadow vertex
      have h := hx.2.2 v
      simp only [show (some (v, true) : Vertex V) = shadow v from rfl, shadow_mem_lift,
        shadow_not_mem_liftApex, shadow_mem_shadows, if_false, if_true, add_zero]
      rw [Finset.sum_filter] at h
      have : (t - 1) / t ≤ ∑ s, if v ∈ s then x s * ((t - 1) / t) else 0 := by
        rw [show (∑ s, if v ∈ s then x s * ((t - 1) / t) else 0) =
          (∑ s, if v ∈ s then x s else 0) * ((t - 1) / t) by
            rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun s _ => by split_ifs <;> simp]
        exact le_mul_of_one_le_left hc h
      have h1 : (t - 1) / t + 1 / t = 1 := by field_simp; ring
      linarith

theorem fracChromaticNumber_mycielski_le [Nonempty V] :
    fracChromaticNumber (graph G) ≤ fracChromaticNumber G + 1 / fracChromaticNumber G := by
  have ha := one_le_fracChromaticNumber (G := G)
  have ha0 : 0 < fracChromaticNumber G := by linarith
  suffices h : fracChromaticNumber (graph G) - 1 / fracChromaticNumber G ≤ fracChromaticNumber G
    by linarith
  refine le_csInf weights_nonempty ?_
  rintro _ ⟨x, hx, rfl⟩
  have hat := fracChromaticNumber_le hx
  have ht : 1 ≤ ∑ s, x s := ha.trans hat
  have ht0 : 0 < ∑ s, x s := by linarith
  have hM := fracChromaticNumber_le (isFracColouring_mycielskiColouring hx ht rfl)
  rw [mycielskiColouring_sum, ← Finset.sum_mul, ← Finset.sum_div] at hM
  have h1 : (∑ s, x s) * ((∑ s, x s - 1) / ∑ s, x s) + (∑ s, x s) / (∑ s, x s) =
      ∑ s, x s := by field_simp; ring
  have h2 : 1 / ∑ s, x s ≤ 1 / fracChromaticNumber G :=
    one_div_le_one_div_of_le ha0 hat
  linarith

/-! ### Lower bound -/

/-- The fractional clique of `M(G)` built from a fractional clique `g` of `G` and `a = χ_f(G)`. -/
noncomputable def mycielskiClique (g : V → ℝ) (a : ℝ) : Vertex V → ℝ
  | none => 1 / a
  | some (v, b) => if b then g v / a else (1 - 1 / a) * g v

theorem sum_mycielskiClique (g : V → ℝ) (a : ℝ) (S : Finset (Vertex V)) :
    ∑ u ∈ S, mycielskiClique g a u = (if none ∈ S then 1 / a else 0) +
      (1 - 1 / a) * ∑ v ∈ univ.filter (fun v => original v ∈ S), g v +
      (∑ v ∈ univ.filter (fun v => shadow v ∈ S), g v) / a := by
  rw [sum_split, Finset.mul_sum, Finset.sum_div]
  simp [mycielskiClique, original, shadow]

theorem isFracClique_mycielskiClique {g : V → ℝ} (hg : IsFracClique G g) {a : ℝ} (ha : 1 ≤ a)
    (hga : ∀ x, IsFracColouring G x → ∀ (T : Finset V) (c : ℝ), 0 ≤ c →
      (∀ s : Finset V, G.IsIndepSet (s : Set V) → ∑ v ∈ T ∩ s, g v ≤ c) →
        ∑ v ∈ T, g v ≤ c * a) :
    IsFracClique (graph G) (mycielskiClique g a) := by
  have ha0 : 0 < a := by linarith
  have hc : 0 ≤ 1 - 1 / a := by
    rw [sub_nonneg, div_le_one ha0]; exact ha
  refine ⟨fun u => ?_, fun S hS => ?_⟩
  · rcases u with _ | ⟨v, _ | _⟩
    · exact div_nonneg zero_le_one ha0.le
    · exact mul_nonneg hc (hg.1 v)
    · exact div_nonneg (hg.1 v) ha0.le
  set J := univ.filter (fun v => original v ∈ S) with hJ
  set K := univ.filter (fun v => shadow v ∈ S) with hK
  rw [sum_mycielskiClique, ← hJ, ← hK]
  -- `J` is independent in `G`
  have hJi : G.IsIndepSet (J : Set V) := by
    intro v hv w hw hvw
    simp only [hJ, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hv hw
    exact hS hv hw (fun h => hvw (by simpa [original] using h))
  -- no edges between `J` and `K`
  have hJK : ∀ j ∈ J, ∀ k ∈ K, ¬ G.Adj j k := by
    intro j hj k hk
    simp only [hJ, hK, mem_filter, mem_univ, true_and] at hj hk
    simpa using hS hj hk (by simp [original, shadow])
  have hgJ : ∑ v ∈ J, g v ≤ 1 := hg.2 J hJi
  have hgJ0 : 0 ≤ ∑ v ∈ J, g v := Finset.sum_nonneg fun v _ => hg.1 v
  by_cases hn : none ∈ S
  · -- the apex excludes every shadow
    have hK0 : K = ∅ := by
      ext k
      simp only [hK, mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro hk
      exact hS hn hk (by simp [shadow]) (apex_adj_shadow G k)
    rw [if_pos hn, hK0, Finset.sum_empty, zero_div, add_zero]
    have : (1 - 1 / a) * ∑ v ∈ J, g v ≤ 1 - 1 / a := mul_le_of_le_one_right hc hgJ
    linarith
  · rw [if_neg hn, zero_add]
    -- `g(K) ≤ g(J) + (1 − g(J)) a`
    have hsplit := Finset.sum_inter_add_sum_sdiff K J g
    have h1 : ∑ v ∈ K ∩ J, g v ≤ ∑ v ∈ J, g v :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        (fun v _ _ => hg.1 v)
    have h2 : ∑ v ∈ K \ J, g v ≤ (1 - ∑ v ∈ J, g v) * a := by
      refine hga _ isFracColouring_singletons (K \ J) _ (by linarith) fun s hs => ?_
      -- `J ∪ ((K \ J) ∩ s)` is independent
      have hdisj : Disjoint J ((K \ J) ∩ s) :=
        Finset.disjoint_left.mpr fun v hvJ hv => (Finset.mem_sdiff.mp
          (Finset.mem_inter.mp hv).1).2 hvJ
      have hind : G.IsIndepSet ((J ∪ (K \ J) ∩ s : Finset V) : Set V) := by
        rw [coe_union, SimpleGraph.IsIndepSet, Set.pairwise_union]
        refine ⟨hJi, fun v hv w hw hvw => hs (Finset.mem_inter.mp hv).2 (Finset.mem_inter.mp hw).2 hvw,
          fun v hv w hw _ => ?_⟩
        have hwK := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hw).1).1
        exact ⟨fun h => hJK v hv w hwK h, fun h => hJK v hv w hwK h.symm⟩
      have := hg.2 _ hind
      rw [Finset.sum_union hdisj] at this
      linarith
    have hKle : ∑ v ∈ K, g v ≤ ∑ v ∈ J, g v + (1 - ∑ v ∈ J, g v) * a := by linarith
    have : (∑ v ∈ K, g v) / a ≤ (∑ v ∈ J, g v) / a + (1 - ∑ v ∈ J, g v) := by
      rw [div_le_iff₀ ha0]
      have : ((∑ v ∈ J, g v) / a + (1 - ∑ v ∈ J, g v)) * a =
          ∑ v ∈ J, g v + (1 - ∑ v ∈ J, g v) * a := by field_simp
      linarith
    have h3 : (1 - 1 / a) * ∑ v ∈ J, g v + (∑ v ∈ J, g v) / a = ∑ v ∈ J, g v := by
      field_simp; ring
    linarith

theorem le_fracChromaticNumber_mycielski [Nonempty V] :
    fracChromaticNumber G + 1 / fracChromaticNumber G ≤ fracChromaticNumber (graph G) := by
  obtain ⟨g, hg, hga⟩ := exists_fracClique_eq (G := G)
  set a := fracChromaticNumber G with ha_def
  have ha : 1 ≤ a := one_le_fracChromaticNumber
  have ha0 : 0 < a := by linarith
  have hM : IsFracClique (graph G) (mycielskiClique g a) :=
    isFracClique_mycielskiClique hg ha fun x hx T c hc hT => by
      have := sum_le_mul_of_indep hg.1 hT hx
      exact le_mul_fracChromaticNumber hc fun y hy => sum_le_mul_of_indep hg.1 hT hy
  have hsum := hM.sum_le_fracChromaticNumber
  rw [show (∑ u, mycielskiClique g a u) = ∑ u ∈ univ, mycielskiClique g a u from rfl,
    sum_mycielskiClique] at hsum
  simp only [mem_univ, ite_true, Finset.filter_true] at hsum
  rw [hga] at hsum
  have : 1 / a + (1 - 1 / a) * a + a / a = a + 1 / a := by field_simp; ring
  linarith

variable (G) in
/-- **Larsen–Propp–Ullman (1995).** For every finite graph `G` with at least one vertex,
`χ_f(M(G)) = χ_f(G) + 1/χ_f(G)`. -/
theorem fracChromaticNumber_mycielski [Nonempty V] :
    fracChromaticNumber (graph G) = fracChromaticNumber G + 1 / fracChromaticNumber G :=
  le_antisymm fracChromaticNumber_mycielski_le le_fracChromaticNumber_mycielski

end FractionalColouring
