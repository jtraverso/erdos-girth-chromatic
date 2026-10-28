/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Fintype.Option

/-!
# The Mycielski construction

The vertices are an apex `none`, original vertices `some (v, false)`, and
shadow vertices `some (v, true)`. Original-original and original-shadow edges
come from the original graph. The apex is adjacent exactly to the shadows.
-/

@[expose] public section

namespace Mycielski

open SimpleGraph

universe u

/-- The two layers of vertices, together with the new apex. -/
abbrev Vertex (V : Type u) := Option (V × Bool)

/-- An original vertex. -/
def original {V : Type u} (v : V) : Vertex V := some (v, false)

/-- The shadow of an original vertex. -/
def shadow {V : Type u} (v : V) : Vertex V := some (v, true)

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

instance {V : Type u} (G : SimpleGraph V) [DecidableRel G.Adj] :
    DecidableRel (graph G).Adj := by
  rintro (_ | ⟨v, bv⟩) (_ | ⟨w, bw⟩) <;>
    (try cases bv) <;> (try cases bw) <;>
    dsimp only [graph, Adj] <;> infer_instance

@[simp] theorem original_adj_original {V : Type u} (G : SimpleGraph V) (v w : V) :
    (graph G).Adj (original v) (original w) ↔ G.Adj v w := Iff.rfl

@[simp] theorem original_adj_shadow {V : Type u} (G : SimpleGraph V) (v w : V) :
    (graph G).Adj (original v) (shadow w) ↔ G.Adj v w := Iff.rfl

@[simp] theorem shadow_adj_original {V : Type u} (G : SimpleGraph V) (v w : V) :
    (graph G).Adj (shadow v) (original w) ↔ G.Adj v w := Iff.rfl

@[simp] theorem not_shadow_adj_shadow {V : Type u} (G : SimpleGraph V) (v w : V) :
    ¬ (graph G).Adj (shadow v) (shadow w) := id

@[simp] theorem shadow_adj_apex {V : Type u} (G : SimpleGraph V) (v : V) :
    (graph G).Adj (shadow v) none := trivial

@[simp] theorem apex_adj_shadow {V : Type u} (G : SimpleGraph V) (v : V) :
    (graph G).Adj none (shadow v) := trivial

/-- The original graph embeds as the original layer. -/
def originalHom {V : Type u} (G : SimpleGraph V) : G →g graph G where
  toFun := original
  map_rel' := id

/-- The original layer is an induced copy of `G`. -/
def originalEmbedding {V : Type u} (G : SimpleGraph V) : G ↪g graph G where
  toFun := original
  inj' := by
    intro v w h
    exact congrArg Prod.fst (Option.some.inj h)
  map_rel_iff' := Iff.rfl

/-- The construction adds one shadow per vertex and one apex. -/
theorem card_vertex {V : Type u} [Fintype V] :
    Fintype.card (Vertex V) = 2 * Fintype.card V + 1 := by
  simp only [Vertex, Fintype.card_option, Fintype.card_prod, Fintype.card_bool]
  omega

/-- A triangle-free graph has no three pairwise adjacent vertices. -/
theorem cliqueFree_three_iff {V : Type u} (G : SimpleGraph V) :
    G.CliqueFree 3 ↔ ∀ v w z, G.Adj v w → G.Adj v z → ¬ G.Adj w z := by
  classical
  constructor
  · intro h v w z hvw hvz hwz
    exact h {v, w, z} (is3Clique_triple_iff.mpr ⟨hvw, hvz, hwz⟩)
  · intro h s hs
    obtain ⟨v, w, z, hvw, hvz, hwz, _⟩ := is3Clique_iff.mp hs
    exact h v w z hvw hvz hwz

/-- Mycielski's construction preserves triangle-freeness. -/
theorem cliqueFree_three {V : Type u} {G : SimpleGraph V} (h : G.CliqueFree 3) :
    (graph G).CliqueFree 3 := by
  rw [cliqueFree_three_iff] at h ⊢
  rintro (_ | ⟨v, bv⟩) (_ | ⟨w, bw⟩) (_ | ⟨z, bz⟩) <;>
    (try cases bv) <;> (try cases bw) <;> (try cases bz) <;>
    simp only [graph, Adj] <;> aesop

/-- Triangle-freeness is both preserved and reflected. -/
theorem graph_cliqueFree_three_iff {V : Type u} (G : SimpleGraph V) :
    (graph G).CliqueFree 3 ↔ G.CliqueFree 3 := by
  constructor
  · intro h
    rw [cliqueFree_three_iff] at h ⊢
    intro v w z hvw hvz hwz
    exact h (original v) (original w) (original z) hvw hvz hwz
  · exact cliqueFree_three

end Mycielski
