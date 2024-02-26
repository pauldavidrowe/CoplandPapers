import CoplandPapers.OnOrderings.ClosureProperties
import CoplandPapers.OnOrderings.OrderDefs

/- 
  This file defines the supports and covers preorders for 
  attack trees. We first define the preorders presented in
  the paper introducing specialization of attack trees. As 
  in the JDG Fest paper, we introduce the covers and supports
  orders for attack trees and we show that these definitions 
  match the origianl specialization orders. 

  We start by introducing the syntax and semantics of
  attack trees. 
-/

-- Syntax of attack trees 
inductive AttackTree (lab : Type)
| atm : lab → AttackTree lab
| or : AttackTree lab → AttackTree lab → AttackTree lab
| and : AttackTree lab → AttackTree lab → AttackTree lab
| seq : AttackTree lab → AttackTree lab → AttackTree lab 

open AttackTree 
variable {lab : Type}

-- Base semantics of attack trees 
@[simp]
def BS : AttackTree lab → Set (QLPO lab)
| .atm s => { qaction s }
| .or t1 t2 => BS t1 ∪ BS t2
| .and t1 t2 => BS t1 ⋈ BS t2
| .seq t1 t2 => BS t1 ↝ BS t2

-- We know that if one singleton is ≤ another then they must be equal
lemma eq_of_action_le {t1 t2 : lab} : action t1 ≤ action t2 → t1 = t2 := by 
  intro le
  obtain ⟨f, hf⟩ := le
  have lt1 : (action t1).l Node.mk = t1 := action_label Node.mk
  have lt2 : (action t2).l Node.mk = t2 := action_label Node.mk
  have := hf.2.1 Node.mk; rwa [←lt1, ←lt2]

-- We can lift the above result to qlpos 
lemma eq_of_qaction_le {t1 t2 : lab} : qaction t1 ≤ qaction t2 → t1 = t2 := by 
  intro le; exact eq_of_action_le le

-- Some facts about the base semantics:

-- The base semantics returns a set of non-empty qlpos 
lemma BS_exists_action {t : AttackTree lab} {l : LPO lab} 
(mem : ⟦l⟧ ∈ BS t) : ∃ _ : l.t, true := by
  revert l
  induction' t
  case atm t
  · intro l mem
    simp [BS] at mem
    rw [LPO.equiv_def] at mem
    let f := Classical.choose mem 
    use f.order.invFun Node.mk
  case or t1 t2 IH1 IH2
  · intros l mem
    simp [BS] at mem
    rcases mem with mem | mem 
    exact IH1 mem
    exact IH2 mem
  case and t1 t2 IH1 _
  · intro l mem
    simp [BS] at mem
    rw [QLPO.mem_dist_prod_iff] at mem
    rcases mem with ⟨a, b, h1, h2, _⟩
    change ⟦l⟧ = ⟦a.merge b⟧ at h1
    simp at h1
    let f := Classical.choose h1 
    specialize IH1 h2
    obtain ⟨a, tr⟩ := IH1
    use f.order.invFun (.inl a)
  case seq t1 t2 IH1 _
  · intro l mem
    simp [BS] at mem
    rcases mem with ⟨q1, q2, h1, _, h3⟩
    cases' (Quotient.exists_rep q1) with l1 hl1
    cases' (Quotient.exists_rep q2) with l2 hl2
    rw [←hl1, ←hl2] at h3; rw [←hl1] at h1
    change ⟦l⟧ = ⟦l1.earlier l2⟧ at h3
    simp at h3
    set f := Classical.choose h3 
    specialize IH1 h1
    obtain ⟨a, tr⟩ := IH1
    use f.order.invFun (toLex (.inl a))

-- Function to extract an event from an element of the base semantics. 
-- Since we just take an element we know exists, it's not constructive. 
noncomputable
def BS_inhabited {t : AttackTree lab} {l : LPO lab}
(mem : ⟦l⟧ ∈ BS t) : Inhabited l.t := by
 constructor
 exact Classical.choose (BS_exists_action mem)

-- The set of qlpos returned by the base semantics is non-empty 
def BS_exists_qlpo (t : AttackTree lab) :
∃ q, q ∈ BS t := by 
  induction' t
  case atm t
  · use (qaction t)
    simp [BS]
  case or t1 t2 IH1 _ 
  · simp [BS]
    obtain ⟨q1, hq⟩ := IH1
    use q1; left; exact hq
  case and t1 t2 IH1 IH2
  · simp [BS]
    obtain ⟨q1, hq1⟩ := IH1
    obtain ⟨q2, hq2⟩ := IH2
    use q1 ⊎ q2
    exact QLPO.merge_mem_dist_prod hq1 hq2
  case seq t1 t2 IH1 IH2
  · simp [BS]
    obtain ⟨q1, hq1⟩ := IH1
    obtain ⟨q2, hq2⟩ := IH2
    use q1 ▷ q2
    exact QLPO.earlier_mem_seq_comp hq1 hq2

-- API for singleton qlpos 
@[simp]
lemma BS_atom_def (t1 : lab) (t2 : QLPO lab) :
t2 ∈ BS (atm t1) ↔ t2 = qaction t1 := by simp [BS]

-- Ideal semantics
-- Notice the extra ι on the atom compared to the paper. 
-- This captures the empty QLPO which I have not ruled out. 
def IS : AttackTree lab → Set (QLPO lab)
| .atm s => (ι { qaction s}).1
| .or t1 t2 => IS t1 ∪ IS t2
| .and t1 t2 => IS t1 ⋈ IS t2
| .seq t1 t2 => ι (IS t1 ↝ IS t2)

-- Filter semantics 
def FS : AttackTree lab → Set (QLPO lab)
| .atm s => (φ { qaction s }).1
| .or t1 t2 => FS t1 ∪ FS t2
| .and t1 t2 => φ (FS t1 ⋈ FS t2)
| .seq t1 t2 => φ (FS t1 ↝ FS t2)

-- The ideal order for attack tree specialization 
def ideal_order : Preorder (AttackTree lab) :=
{ le := λ t1 t2 => IS t1 ⊆ IS t2
  le_refl := fun a ⦃a_1⦄ a => a
  le_trans := by 
    intro a b c le1 le2
    simp at *; exact fun ⦃a_1⦄ a => le2 (le1 a) 
}

-- API for the ideal order 
lemma ideal_order_le_def (t1 t2 : AttackTree lab) :
ideal_order.le t1 t2 ↔ IS t1 ⊆ IS t2 := by rfl 

-- Notation for the ideal order 
infix:50 " ≼ι " => ideal_order.le 

-- The filter order for attack tree specialization 
def filter_order : Preorder (AttackTree lab) := 
{ le := λ t1 t2 => FS t1 ⊆ FS t2
  le_refl := fun a ⦃a_1⦄ a => a
  le_trans := by 
    intro a b c le1 le2
    simp at *; exact fun ⦃a_1⦄ a => le2 (le1 a) 
}

-- API for the filter order 
lemma filter_order_le_def (t1 t2 : AttackTree lab) : 
filter_order.le t1 t2 ↔ FS t1 ⊆ FS t2 := by rfl 

-- Notation for the filter order 
infix:50 " ≼φ " => filter_order.le 

-- Theorem 1 of JDG Fest 
theorem IS_eq_lower_BS (t : AttackTree lab) : 
IS t = ι (BS t) := by
  induction' t
  case atm t
  · simp [IS, BS]
  case or t1 t2 IH1 IH2
  · simp [IS, BS] at *; rw [IH1, IH2]
  case and t1 t2 IH1 IH2
  · simp [IS]; rw [IH1, IH2]
    rw [←QLPO.lower_dist_prod _ _]
  case seq t1 t2 IH1 IH2
  · unfold IS; rw [IH1, IH2]
    rw [←QLPO.lower_seq_comp _ _]
    simp [BS]

--Theorem 2 of JDG Fest 
theorem FS_eq_upper_BS (t : AttackTree lab) :
FS t = φ (BS t) := by
  induction' t
  case atm t
  · simp [FS, BS]
  case or t1 t2 IH1 IH2
  · simp [FS, BS] at *; rw [IH1, IH2]
  case and t1 t2 IH1 IH2
  · dsimp only [FS]; rw [IH1, IH2]
    rw [←QLPO.upper_dist_prod _ _]
    simp [BS]
  case seq t1 t2 IH1 IH2
  · dsimp only [FS]; rw [IH1, IH2]
    rw [←QLPO.upper_seq_comp _ _]
    simp [BS]

-- First half of Theorem 3 of JDG Fest 
theorem lower_subset_iff_covers (S T : Set (QLPO lab)) :
((ι S) : Set (QLPO lab)) ⊆ ι T ↔ Covers T S := by 
  constructor <;> intro mem
  · observe Slt : S ⊆ ι T
    simp at Slt ⊢
    intro H Hmem 
    specialize Slt Hmem
    exact Slt
  · simp at mem
    intro K Kmem; simp at Kmem
    obtain ⟨H, hH⟩ := Kmem
    specialize mem H hH.1
    obtain ⟨G, hG⟩ := mem
    simp; use G, hG.1
    exact le_trans hH.2 hG.2

-- Second half of Theorem 3 of JDG Fest 
theorem upper_subset_iff_supports (S T : Set (QLPO lab)) :
((φ S) : Set (QLPO lab)) ⊆ φ T ↔ Supports T S := by 
  constructor <;> intro mem
  · observe Slt : S ⊆ φ T
    simp at Slt ⊢
    intro H Hmem
    specialize Slt Hmem
    exact Slt
  · simp at mem
    intro K Kmem; simp at Kmem
    obtain ⟨H, hH⟩ := Kmem
    specialize mem H hH.1
    obtain ⟨G, hG⟩ := mem
    simp; use G, hG.1
    exact le_trans hG.2 hH.2

-- First part of Corollary 1
theorem lower_lt_iff_covers (t1 t2 : AttackTree lab) : 
t1 ≼ι t2 ↔ Covers (BS t2) (BS t1) := by 
  rw [ideal_order_le_def, IS_eq_lower_BS, IS_eq_lower_BS]
  exact lower_subset_iff_covers _ _

-- Second part of Corollary 1
theorem upper_lt_iff_supports (t1 t2 : AttackTree lab) : 
t1 ≼φ t2 ↔ Supports (BS t2) (BS t1) := by 
  rw [filter_order_le_def, FS_eq_upper_BS, FS_eq_upper_BS]
  exact upper_subset_iff_supports _ _

-- The covers preorder for attack trees 
def AT.covers_preorder (lab : Type) : Preorder (AttackTree lab) :=
  General.covers_preorder BS

-- The supports preorder for attack trees 
def AT.supports_preorder (lab : Type) : Preorder (AttackTree lab) := 
  General.supports_preorder BS 

-- API for the covers preorder 
lemma AT.covers_preorder_def {lab : Type} (t1 t2 : AttackTree lab) : 
(AT.covers_preorder lab).le t1 t2 ↔ Covers (BS t2) (BS t1) := by rfl 

-- API for the supports preorder 
lemma AT.supports_preorder_def {lab : Type} (t1 t2 : AttackTree lab) :
(AT.supports_preorder lab).le t1 t2 ↔ Supports (BS t2) (BS t1) := by rfl 
