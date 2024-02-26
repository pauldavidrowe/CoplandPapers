import CoplandPapers.OnOrderings.CoplandOrder
import CoplandPapers.OnOrderings.AttackTrees

namespace Covers 
open AttackTree 
variable {lab : Type} {p : Place}
/- 
  Type synonym for attack trees ordered by the Covers Preorder
  Without the type synonyms, the instances for the Covers order 
  and the supports order will conflict. 

  This was originally to avoid confining the order instances to 
  sections, but sections turn out to be necessary after all. 
  The rest of this might be simplified or easier to read without
  these type synonyms. But we're stuck with them for now.   
-/
abbrev AttCov (lab : Type) := AttackTree lab 

-- Tell Lean AttCov forms a Preorder
local instance : Preorder (AttCov lab) := AT.covers_preorder lab 

-- Type synonym for Copland phrases at a given Place p,
-- ordered by the Covers Preorder
abbrev CopCov (_ : Place) := Copland 

-- Tell lean CopCov forms a Preorder
local instance : Preorder (CopCov p) := Copland.covers_preorder p 

-- Un-named section helps deconflict order instances 
section

-- Automatically reinterprets AttCov as AttackTree
-- Lean 3 needed to mark it as (locally?) reducible. 
-- Since we changed AttCov to an abbreviation, it's automatically 
-- reducible. Keeping this here in case the abbreviation causes
-- unforeseen trouble in later files
--attribute [local reducible] AttCov

-- API for ≤ on attack trees 
lemma AT.le_def {t1 t2 : AttackTree lab} : 
t1 ≤ t2 ↔ 
∀ H, H ∈ BS t1 → (∃ G, G ∈ BS t2 ∧ H ≤ G) := by rfl 

-- API for ≤ on Copland phrases 
lemma Cop.le_def {c1 c2 : CopCov p} : 
c1 ≤ c2 ↔ ∀ H, H ∈ copland_base_sem p c1 → 
(∃ G, G ∈ copland_base_sem p c2 ∧ H ≤ G) := by rfl 

-- Atoms order by ≤ must be equal 
lemma atom_le_atom {t1 t2 : lab} : 
  (atm t1) ≤ (atm t2) → t1 = t2 := by
  intro le; rw [AT.le_def] at le
  specialize le (qaction t1) (by simp [BS])
  rcases le with ⟨t2a, t2amem, le⟩
  simp [BS] at t2amem; subst t2amem
  change qaction t1 ≤ qaction t2 at le
  exact eq_of_qaction_le le

-- An atom ≤ t1 ∨ t2 must be ≤ t1 or ≤ t2
lemma atom_le_or {t1 : lab} {t21 t22 : AttackTree lab} 
(le : (atm t1) ≤ (t21.or t22)) :
(atm t1) ≤ t21 ∨ (atm t1) ≤ t22 := by 
  rw [AT.le_def] at le ⊢
  specialize le (qaction t1) (by simp [BS])
  rcases le with ⟨t2, t2mem, le⟩
  cases t2mem with
  | inl t2mem =>
    left
    intro H Hmem; simp at Hmem; subst Hmem
    use t2, t2mem; exact le
  | inr t2mem =>
    right
    intro H Hmem; simp at Hmem; subst Hmem
    use t2, t2mem; exact le

-- An atom ≤ t1 ∧ t2 must be ≤ t1 or t2
lemma atom_le_and {t1 : lab} {t21 t22 : AttackTree lab}
(le : (atm t1) ≤ t21.and t22) :
(atm t1) ≤ t21 ∨ (atm t1) ≤ t22 := by 
  rw [AT.le_def] at le ⊢; rw [AT.le_def]
  specialize le (qaction t1) (by simp [BS])
  rcases le with ⟨t2, t2mem, le⟩
  simp [BS, (· ⋈ ·)] at t2mem
  rcases t2mem with ⟨t3, t3mem, ⟨t4, t4mem, eq⟩⟩
  subst eq
  replace le := QLPO.merge.le_left_or_right_of_singleton le
  cases le with 
  | inl le => 
    left
    intro H Hmem; simp [BS] at Hmem; subst Hmem
    use t3, t3mem, le
  | inr le => 
    right
    intro H Hmem; simp [BS] at Hmem; subst Hmem
    use t4, t4mem, le

-- If t1 ∨ t2 ≤ an atom, then either t1 ≤ atom or t2 ≤ atom 
lemma or_le_atom {t11 t12 : AttackTree lab} {t2 : lab}
(le : t11.or t12 ≤ atm t2) : t11 ≤ atm t2 ∧ t12 ≤ atm t2 := by
  rw [AT.le_def] at le
  constructor
  all_goals  
    intro H Hmem; 
    have Hmem' : H ∈ BS (t11.or t12); simp [BS]; tauto
    exact le H Hmem'

end -- end unnamed section
end Covers
