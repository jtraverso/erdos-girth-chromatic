/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Graphs of large girth and large chromatic number: Erdős, Mycielski, Larsen–Propp–Ullman

**Erdős (1959).** For every `g` and every `k` there is a finite graph with girth greater than `g`
and chromatic number greater than `k`. Erdős proved this with the probabilistic method, and the
proof gives more: for every `ε > 0` and all large `n` there is a graph on `n` vertices with girth
greater than `g` whose independent sets all have fewer than `ε n` vertices.

* `ErdosGirthChromatic.exists_girth_indep`: for every `g` and `ε > 0`, for all sufficiently large `n` there
  is a graph on `Fin n` with extended girth (Mathlib's `SimpleGraph.egirth`) greater than `g` in
  which every independent set has fewer than `ε n` vertices.
* `ErdosGirthChromatic.exists_girth_not_colorable`: for every `g` and `k`, for all sufficiently large `n`
  there is a graph on `Fin n` with girth greater than `g` that is not `k`-colourable.
* `ErdosGirthChromatic.exists_girth_chromaticNumber`: **Erdős' theorem.** For every `g` and `k` there is a
  finite graph with girth greater than `g` and chromatic number greater than `k`.

**Mycielski (1955)** gives the explicit construction for girth four. The Mycielski graph `M(G)` has
an original and a shadow copy of each vertex of `G` and an apex adjacent to the shadows; the other
edges follow `G` (namespace `Mycielski`): `M(G)` is triangle-free iff `G` is, `M(G)` is
`(k+1)`-colourable iff `G` is `k`-colourable, `χ(M(G)) = χ(G) + 1` for finite `G`, and iterating from
`K₂` gives triangle-free graphs with `3·2ⁿ − 1` vertices and chromatic number `n + 2`.

**Larsen, Propp and Ullman (1995).** For the fractional chromatic number `χ_f` (the least total
weight of a fractional colouring by independent sets, defined below in namespace
`FractionalColouring`), every finite graph `G` with at least one vertex satisfies
`χ_f(M(G)) = χ_f(G) + 1/χ_f(G)` (`FractionalColouring.fracChromaticNumber_mycielski`). Consequently,
along the Mycielski family the chromatic number grows by one at each step while the fractional
chromatic number follows `a ↦ a + 1/a` (an informal remark, not a formal statement here).

The Mathlib definitions used in these statements are reproduced verbatim, with file and line at the
pinned Mathlib revision, in `MATHLIB_DEFINITIONS.md` at the root of this repository.
-/

@[expose] public section

open Finset SimpleGraph

namespace ErdosGirthChromatic

/-- **Erdős (1959), structural form.** For every `g` and every `ε > 0`, for all sufficiently large
`n` there is a graph on `n` vertices with no cycle of length at most `g` in which every independent
set has fewer than `ε n` vertices. -/
theorem exists_girth_indep (g : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ G : SimpleGraph (Fin n), (g : ℕ∞) < G.egirth ∧
      ∀ s : Finset (Fin n), G.IsIndepSet (s : Set (Fin n)) → (s.card : ℝ) < ε * n := by
  sorry

/-- For every `g` and `k`, for all sufficiently large `n` there is a graph on `n` vertices with
no cycle of length at most `g` that is not `k`-colourable. -/
theorem exists_girth_not_colorable (g k : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ G : SimpleGraph (Fin n), (g : ℕ∞) < G.egirth ∧ ¬ G.Colorable k := by
  sorry

/-- **Erdős' theorem (1959).** For every `g` and `k` there is a finite graph with girth greater
than `g` and chromatic number greater than `k`. -/
theorem exists_girth_chromaticNumber (g k : ℕ) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)), (g : ℕ∞) < G.egirth ∧ (k : ℕ∞) < G.chromaticNumber := by
  sorry

end ErdosGirthChromatic

namespace Mycielski
open SimpleGraph
universe u

/-- The two layers of vertices, together with the new apex. -/
abbrev Vertex (V : Type u) := Option (V × Bool)

/-- Adjacency in the Mycielski construction. -/
def Adj {V : Type u} (G : SimpleGraph V) : Vertex V → Vertex V → Prop
  | some (v, false), some (w, false) => G.Adj v w
  | some (v, false), some (w, true) => G.Adj v w
  | some (v, true), some (w, false) => G.Adj v w
  | none, some (_, true) => True
  | some (_, true), none => True
  | _, _ => False

/-- The Mycielski graph of `G`. -/
def graph {V : Type u} (G : SimpleGraph V) : SimpleGraph (Vertex V) where
  Adj := Adj G
  symm := ⟨by
    rintro (_ | ⟨v, bv⟩) (_ | ⟨w, bw⟩) <;>
      (try cases bv) <;> (try cases bw) <;>
      simp only [Adj] <;> first | exact id | exact G.adj_symm⟩
  loopless := ⟨by
    rintro (_ | ⟨v, b⟩)
    · simp [Adj]
    · cases b <;> simp [Adj]⟩

/-- Vertex types of the iterated construction, starting from `K₂`. -/
def FamilyVertex : ℕ → Type
  | 0 => Fin 2
  | n + 1 => Vertex (FamilyVertex n)

instance familyVertexFintype : (n : ℕ) → Fintype (FamilyVertex n)
  | 0 => inferInstanceAs (Fintype (Fin 2))
  | n + 1 => by
    letI := familyVertexFintype n
    exact inferInstanceAs (Fintype (Vertex (FamilyVertex n)))

/-- The explicit Mycielski family. -/
def family : (n : ℕ) → SimpleGraph (FamilyVertex n)
  | 0 => ⊤
  | n + 1 => graph (family n)

/-- The construction adds one shadow per vertex and one apex. -/
theorem card_vertex {V : Type u} [Fintype V] :
    Fintype.card (Vertex V) = 2 * Fintype.card V + 1 := by
  sorry

/-- Triangle-freeness is both preserved and reflected. -/
theorem graph_cliqueFree_three_iff {V : Type u} (G : SimpleGraph V) :
    (graph G).CliqueFree 3 ↔ G.CliqueFree 3 := by
  sorry

/-- Mycielski's coloring theorem, expressed using finite palettes. -/
theorem colorable_succ_iff {V : Type u} (G : SimpleGraph V) (k : ℕ) :
    (graph G).Colorable (k + 1) ↔ G.Colorable k := by
  sorry

/-- The chromatic number of a finite graph increases by exactly one. -/
theorem chromaticNumber_graph {V : Type u} [Finite V] (G : SimpleGraph V) :
    (graph G).chromaticNumber = G.chromaticNumber + 1 := by
  sorry

/-- The family has `3 * 2^n - 1` vertices, without truncated subtraction. -/
theorem card_familyVertex (n : ℕ) :
    Fintype.card (FamilyVertex n) + 1 = 3 * 2 ^ n := by
  sorry

/-- Every graph in the explicit family is triangle-free. -/
theorem family_cliqueFree_three (n : ℕ) : (family n).CliqueFree 3 := by
  sorry

/-- Exact chromatic numbers of the explicit family. -/
theorem family_chromaticNumber (n : ℕ) : (family n).chromaticNumber = (n + 2 : ℕ) := by
  sorry

/-- Finite triangle-free graphs have unbounded chromatic number. -/
theorem exists_triangleFree_chromaticNumber_ge (k : ℕ) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)), G.CliqueFree 3 ∧ (k : ℕ∞) ≤ G.chromaticNumber := by
  sorry

end Mycielski

namespace FractionalColouring

/-- A fractional colouring: nonnegative weights on vertex sets, vanishing off independent
sets, covering every vertex with total weight at least `1`. -/
def IsFracColouring {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (x : Finset V → ℝ) : Prop :=
  (∀ s, 0 ≤ x s) ∧ (∀ s : Finset V, ¬ G.IsIndepSet (s : Set V) → x s = 0) ∧
    ∀ v, 1 ≤ ∑ s ∈ univ.filter (fun s => v ∈ s), x s

/-- The fractional chromatic number `χ_f(G)`. -/
noncomputable def fracChromaticNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℝ :=
  sInf {t | ∃ x, IsFracColouring G x ∧ t = ∑ s, x s}

/-- **Larsen–Propp–Ullman (1995).** For every finite graph `G` with at least one vertex,
`χ_f(M(G)) = χ_f(G) + 1/χ_f(G)`. -/
theorem fracChromaticNumber_mycielski {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [Nonempty V] :
    fracChromaticNumber (Mycielski.graph G) = fracChromaticNumber G + 1 / fracChromaticNumber G := by
  sorry

end FractionalColouring
