/-
Copyright (c) 2024 Paul D. Rowe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul D. Rowe
-/
import Mathlib.Tactic

-- A general version of Covers not tied to any specific structure
@[simp]
def Covers {β : Type*} [Preorder β] (S T : Set β) :=
∀ H, H ∈ T → ∃ G, G ∈ S ∧ H ≤ G

-- A general version of Supports not tied to any specific structure
@[simp]
def Supports {β : Type*} [Preorder β] (S T : Set β) :=
∀ H, H ∈ T → ∃ G, G ∈ S ∧ G ≤ H

-- The Preorder defined by the Covers relation
def General.covers_preorder {α β : Type*} [Preorder β] (bs : α → Set β) : Preorder α :=
{ le := λ a1 a2 => Covers (bs a2) (bs a1)
  le_refl := by intros a H mem; use H, mem
  le_trans := by
   intros a b c le1 le2
   simp at *; intro H Hmem
   specialize le1 H Hmem
   obtain ⟨K, hK⟩ := le1
   specialize le2 K hK.1
   obtain ⟨G, hG⟩ := le2
   use G, hG.1
   exact le_trans hK.2 hG.2
}

-- The Preorder devined by the Supports relation
def General.supports_preorder {α β : Type*} [Preorder β] (bs : α → Set β) : Preorder α :=
{ le := λ a b => Supports (bs b) (bs a)
  le_refl := by
   simp; intro a H mem; use H, mem
  le_trans := by
    intro a b c le1 le2
    simp at *; intro H Hmem
    specialize le1 H Hmem
    obtain ⟨K, hK⟩ := le1
    specialize le2 K hK.1
    obtain ⟨G, hG⟩ := le2
    use G, hG.1
    exact le_trans hG.2 hK.2
}

-- API for working with Covers
lemma Covers.preorder_def {α β : Type*} [Preorder β] (bs : α → Set β) (a1 a2 : α) :
(General.covers_preorder bs).le a1 a2 ↔ Covers (bs a2) (bs a1) := by rfl

-- API for working with Supports
lemma Supports.preorder_def {α β : Type*} [Preorder β] (bs : α → Set β) (a1 a2 : α) :
(General.supports_preorder bs).le a1 a2 ↔ Supports (bs a2) (bs a1) := by rfl
