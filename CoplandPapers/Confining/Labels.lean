import Mathlib.Tactic

-- This file defines labels and contains simple 
-- facts about them. 

-- A Component is a Program at a Place
inductive Place  
| pl : String → Place



noncomputable 
instance : DecidableEq Place := Classical.decEq Place

inductive Program 
| pr : String → Program 

inductive Component : Type 
| c : Place → Program → Component 

inductive Label : Type 
| msp : Component → Component → Label 
| req : Place → Place → Label 
| rpy : Place → Place → Label 
| split : Label 
| joins : Label 
| joinp : Label 
| sig : Label 
| hsh : Label 
| nul : Label 
| cpy : Label 
| cor : Component → Label 
| rep : Component → Label 
open Label

inductive ALabel : Type 
| msp : Component → Component → ALabel
| sig : ALabel
| hsh : ALabel
| nul : ALabel
| cpy : ALabel

inductive MSLab : Label → Prop 
| meas {c₁ c₂ : Component}: MSLab (msp c₁ c₂) 

@[simp]
def MSLab' (l : Label) : Prop :=
∃ c₁ c₂, l = msp c₁ c₂ 

lemma ms_lab_ms_lab' :
∀ l, MSLab l ↔ MSLab' l := by
  intro l 
  constructor <;> intro h 
  · cases h with 
    | @meas c1 c2 => use c1, c2
  · obtain ⟨c1, ⟨c2, hcs⟩⟩ := h 
    rw [hcs]
    exact MSLab.meas

inductive AdvLab : Label → Prop 
| cevt {c : Component} : AdvLab (cor c)
| revt {c : Component} : AdvLab (rep c)

@[simp]
def AdvLab' (l : Label) : Prop :=
∃ c, l = cor c ∨ l = rep c 

lemma adv_lab_adv_lab' (l : Label):
AdvLab l ↔ AdvLab' l := by 
  cases' l with c1 c2 c1 c2 c1 c2 c c 
  case cor
  · constructor <;> intro; use c; left; rfl; constructor
  case rep
  · constructor <;> intro; use c; right; rfl; exact AdvLab.revt
  all_goals
  · constructor <;> intro h 
    cases' h 
    obtain ⟨w, h⟩ := h 
    cases' h with h h <;> cases' h 

lemma adv_lab_def {l : Label} : 
AdvLab l ↔ ∃ c, l = cor c ∨ l = rep c := by rw [adv_lab_adv_lab']; simp

