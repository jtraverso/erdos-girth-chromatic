/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mycielski.Coloring

/-!
# An explicit family of triangle-free graphs of unbounded chromatic number

Start with `K₂` and iterate the Mycielski construction. The `n`th graph is
triangle-free and has chromatic number `n + 2`.
-/

@[expose] public section

namespace Mycielski

open SimpleGraph

/-- Vertex types of the iterated construction, starting from `K₂`. -/
def FamilyVertex : ℕ → Type
  | 0 => Fin 2
  | n + 1 => Vertex (FamilyVertex n)

instance familyVertexFintype : (n : ℕ) → Fintype (FamilyVertex n)
  | 0 => inferInstanceAs (Fintype (Fin 2))
  | n + 1 => by
    letI := familyVertexFintype n
    exact inferInstanceAs (Fintype (Vertex (FamilyVertex n)))

instance familyVertexNonempty : (n : ℕ) → Nonempty (FamilyVertex n)
  | 0 => ⟨(0 : Fin 2)⟩
  | _ + 1 => ⟨none⟩

/-- The family has `3 * 2^n - 1` vertices, without truncated subtraction. -/
theorem card_familyVertex (n : ℕ) :
    Fintype.card (FamilyVertex n) + 1 = 3 * 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    change Fintype.card (Vertex (FamilyVertex n)) + 1 = _
    rw [card_vertex, Nat.pow_succ, ← Nat.mul_assoc, ← ih]
    omega

/-- The explicit Mycielski family. -/
def family : (n : ℕ) → SimpleGraph (FamilyVertex n)
  | 0 => ⊤
  | n + 1 => graph (family n)

/-- Every graph in the explicit family is triangle-free. -/
theorem family_cliqueFree_three (n : ℕ) : (family n).CliqueFree 3 := by
  induction n with
  | zero =>
    intro s hs
    have hcard := hs.card_eq
    have hle := Finset.card_le_univ s
    change s.card ≤ Fintype.card (Fin 2) at hle
    simp only [Fintype.card_fin] at hle
    omega
  | succ n ih => exact cliqueFree_three ih

/-- Exact chromatic numbers of the explicit family. -/
theorem family_chromaticNumber (n : ℕ) : (family n).chromaticNumber = (n + 2 : ℕ) := by
  induction n with
  | zero =>
    change (⊤ : SimpleGraph (Fin 2)).chromaticNumber = (2 : ℕ∞)
    simp
  | succ n ih =>
    change (graph (family n)).chromaticNumber = _
    rw [chromaticNumber_graph, ih]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    ac_rfl

/-- Finite triangle-free graphs have unbounded chromatic number. -/
theorem exists_triangleFree_chromaticNumber_ge (k : ℕ) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)), G.CliqueFree 3 ∧ (k : ℕ∞) ≤ G.chromaticNumber := by
  classical
  let e := Fintype.equivFin (FamilyVertex k)
  let G := (family k).map e.toEmbedding
  refine ⟨_, G, ?_, ?_⟩
  · exact (cliqueFree_map_iff).mpr (family_cliqueFree_three k)
  · have hmono := chromaticNumber_mono_of_hom (Hom.map e (family k)
      (fun {u v} h heq => (family k).ne_of_adj h (e.injective heq)))
    have hk : (k : ℕ∞) ≤ (family k).chromaticNumber := by
      rw [family_chromaticNumber]
      exact_mod_cast (Nat.le_add_right k 2)
    exact hk.trans hmono

end Mycielski
