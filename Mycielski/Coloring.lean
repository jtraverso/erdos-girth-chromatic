/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mycielski.Basic
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Colorings of the Mycielski graph

An existing coloring extends by giving shadows the color of their originals
and using a fresh color at the apex. Conversely, the apex color can be
eliminated from the original layer by recoloring with shadow colors.
-/

@[expose] public section

namespace Mycielski

open SimpleGraph

universe u v

/-- Extend a coloring with a fresh apex color. -/
def liftColoring {V : Type u} {C : Type v} {G : SimpleGraph V}
    (c : G.Coloring C) : (graph G).Coloring (Option C) :=
  Coloring.mk
    (fun x => match x with
      | none => none
      | some (v, _) => some (c v)) (by
        have hc : ∀ {v w}, G.Adj v w → c v ≠ c w := c.valid
        rintro (_ | ⟨v, bv⟩) (_ | ⟨w, bw⟩) <;>
          (try cases bv) <;> (try cases bw) <;>
          simp only [graph, Adj] <;> aesop)

/-- The extra color suffices for the Mycielski graph. -/
theorem colorable_succ {V : Type u} {G : SimpleGraph V} {k : ℕ}
    (h : G.Colorable k) : (graph G).Colorable (k + 1) := by
  obtain ⟨c⟩ := h
  exact ⟨(graph G).recolorOfEquiv (finSuccEquiv k).symm (liftColoring c)⟩

/-- Remove the apex color from a coloring of the original layer. -/
noncomputable def lowerColoring {V : Type u} {C : Type v} {G : SimpleGraph V}
    (c : (graph G).Coloring C) : G.Coloring {a : C // a ≠ c none} := by
  classical
  let f : V → C := fun v =>
    if c (original v) = c none then c (shadow v) else c (original v)
  have hf (v : V) : f v ≠ c none := by
    dsimp [f]
    split
    · exact c.valid (shadow_adj_apex G v)
    · assumption
  refine Coloring.mk (fun v => ⟨f v, hf v⟩) ?_
  intro v w hvw heq
  have heq' : f v = f w := congrArg Subtype.val heq
  dsimp [f] at heq'
  split_ifs at heq' with hv hw hw
  · exact c.valid ((original_adj_original G v w).mpr hvw) (hv.trans hw.symm)
  · exact c.valid ((shadow_adj_original G v w).mpr hvw) heq'
  · exact c.valid ((original_adj_shadow G v w).mpr hvw) heq'
  · exact c.valid ((original_adj_original G v w).mpr hvw) heq'

/-- Any `(k+1)`-coloring of the Mycielski graph yields a `k`-coloring of `G`. -/
theorem colorable_of_colorable_succ {V : Type u} {G : SimpleGraph V} {k : ℕ}
    (h : (graph G).Colorable (k + 1)) : G.Colorable k := by
  obtain ⟨c⟩ := h
  exact ⟨G.recolorOfEquiv (finSuccAboveEquiv (c none)).symm (lowerColoring c)⟩

/-- Mycielski's coloring theorem, expressed using finite palettes. -/
theorem colorable_succ_iff {V : Type u} (G : SimpleGraph V) (k : ℕ) :
    (graph G).Colorable (k + 1) ↔ G.Colorable k :=
  ⟨colorable_of_colorable_succ, colorable_succ⟩

/-- The chromatic number of a finite graph increases by exactly one. -/
theorem chromaticNumber_graph {V : Type u} [Finite V] (G : SimpleGraph V) :
    (graph G).chromaticNumber = G.chromaticNumber + 1 := by
  let k := G.chromaticNumber.toNat
  have hk : G.chromaticNumber = (k : ℕ∞) :=
    (ENat.natCast_toNat
      ((chromaticNumber_ne_top_iff_exists).mpr
        ⟨_, colorable_chromaticNumber_of_fintype G⟩)).symm
  have hupper : (graph G).chromaticNumber ≤ ((k + 1 : ℕ) : ℕ∞) :=
    (colorable_succ (colorable_chromaticNumber_of_fintype G)).chromaticNumber_le
  have hlower : ((k + 1 : ℕ) : ℕ∞) ≤ (graph G).chromaticNumber := by
    apply le_chromaticNumber_iff_colorable.mpr
    intro m hm
    cases m with
    | zero =>
      have := hm.isEmpty
      exact isEmptyElim (none : Vertex V)
    | succ m =>
      have hgm := (colorable_succ_iff G m).mp hm
      have hkm : k ≤ m := by
        have := hgm.chromaticNumber_le
        rw [hk] at this
        exact_mod_cast this
      exact Nat.succ_le_succ hkm
  apply le_antisymm
  · simpa only [hk, Nat.cast_add, Nat.cast_one] using hupper
  · simpa only [hk, Nat.cast_add, Nat.cast_one] using hlower

end Mycielski
