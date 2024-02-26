import CoplandPapers.OnOrderings.ClosureProperties 
import CoplandPapers.OnOrderings.OrderDefs 

/-
  This file works up to defining the covers and supports
  orders on Copland phrases. This does not leverage any prior 
  definition of Copland syntax or semantics, so we develop just 
  what we need to proceed. 
-/

-- The current set of Copland ASPs. 
inductive ASP 
| msp : Component → Component → ASP
--| nul : ASP 
| cpy : ASP 
| hsh : ASP 
| sig : ASP 

-- The labels to be associated with each ASP 
def asp_label (a : ASP) : Label :=
match a with 
| (ASP.msp c1 c2) => Label.msp c1 c2 
--| (ASP.nul) => Label.nul 
| (ASP.cpy) => Label.cpy 
| (ASP.hsh) => Label.hsh 
| (ASP.sig) => Label.sig 

-- Predicate to recognize labels as pertaining to ASPs 
@[simp]
def IsASPLabel (lab : Label) : Prop :=
match lab with 
| (Label.msp _ _) => true 
| (Label.nul) => true
| (Label.cpy) => true 
| (Label.hsh) => true 
| (Label.sig) => true 
| _ => false 

-- Sequence of utility lemmas showing that other
-- labels we will encounter are not ASP labels 
@[simp]
lemma asp_label_ne_split (a : ASP) : 
asp_label a ≠ Label.split := by
  cases a <;> intro h <;> cases h

@[simp]
lemma asp_label_ne_joins (a : ASP) : 
asp_label a ≠ Label.joins := by
  cases a <;> intro h <;> cases h

@[simp]
lemma asp_label_ne_req (a : ASP) (p q : Place) : 
asp_label a ≠ Label.req p q := by
  cases a <;> intro h <;> cases h

@[simp]
lemma asp_label_ne_rpy (a : ASP) (p q : Place) :
asp_label a ≠ Label.rpy p q := by
  cases a <;> intro h <;> cases h

lemma asp_label_not_adv (a : ASP) :
¬ AdvLab (asp_label a) := by
  cases a; all_goals { rw [adv_lab_adv_lab']; simp [asp_label] }

-- The directions for branching
inductive Dir 
| pos : Dir 
| neg : Dir 

-- The Split specification for branching 
inductive Split
| mk : Dir → Dir → Split 

def split_fst : Split → Dir :=
λ s => match s with 
| ⟨d1, _⟩ => d1

def split_snd : Split → Dir := 
λ s => match s with 
| ⟨_, d2⟩ => d2

-- Copland syntax 
inductive Copland 
| atom : ASP → Copland
| lseq : Copland → Copland → Copland
| bseq : Split → Copland → Copland → Copland
| bpar : Split → Copland → Copland → Copland 
| att : Place → Copland → Copland 
open Copland 

/- 
  Since we are using lpos as the unifying object between
  Copland and attack trees, we define the semantics in 
  terms of lpos. 

  Note that LPO is slightly different from exec as defined
  in execs.lean. We might consider refactoring the files 
  for the Confining paper to use EvSys as defined here 
  instead of execs. 
-/
def EvSys := LPO Label 

-- Event systems inherit the partial order structure of lpos
instance EvSys.preorder : Preorder EvSys := LPO.Preorder

-- Construction of a singleton EvSys from a Label 
def evsys_of_label : Label → EvSys :=
λ lab =>
{ t := Node
  fin := Node.Fintype
  po := 
  { le := (· = ·)
    le_refl := by simp
    le_trans := by intro; simp at *;
    le_antisymm := by simp
  }
  l := λ _ => lab,
}

-- Extracts the Label from a singleton built from the Label 
@[simp]
lemma label_of_evsys_of_label {l : Label} 
{val : (evsys_of_label l).t}:
(evsys_of_label l).l val = l := by rfl 

-- The event semantics of a Copland phrase 
@[simp]
def cop_sem : Place → Copland → EvSys 
| _, (atom a) =>
    action (asp_label a) 
| p, (lseq c1 c2) => 
    LPO.earlier (cop_sem p c1) (cop_sem p c2)
| p, (bseq _ c1 c2) =>
    LPO.earlier (evsys_of_label Label.split) 
    (LPO.earlier (LPO.earlier (cop_sem p c1) (cop_sem p c2))
                  (evsys_of_label Label.joins))
| p, (bpar _ c1 c2) => 
    LPO.earlier (evsys_of_label Label.split) 
    (LPO.earlier (LPO.merge (cop_sem p c1) (cop_sem p c2))
                  (evsys_of_label Label.joins))
| p, (att q c1) => LPO.earlier (evsys_of_label (Label.req p q)) 
                 (LPO.earlier (cop_sem q c1) (evsys_of_label (Label.req p q)))

-- Show that the EvSys of a Copland phrase is non-empty
def cop_sem_inhabited (p : Place) (c : Copland) :
Inhabited (cop_sem p c).t :=
{default := 
  match c with
  | atom _ => Node.mk
  | lseq c1 _ => .inl (cop_sem_inhabited p c1).default 
  | bseq _ c1 _ => .inr (.inl (.inl (cop_sem_inhabited p c1).default))
  | bpar _ c1 _ => .inr (.inl (.inl (cop_sem_inhabited p c1).default))
  | att q c1 => .inr (.inl (cop_sem_inhabited q c1).default)
}
 

-- Since the generic definitions are in terms of sets of qlpos,
-- we lift the Copland semantics to return a set and not just an LPO. 
@[simp]
def copland_base_sem (p : Place) (c : Copland) : Set (QLPO Label) :=
{ ⟦cop_sem p c⟧ }

-- The set produced above is always non-empty
lemma copland_base_sem_exists_qlpo (p : Place) :
  ∀ (c : Copland), ∃ (G : QLPO Label), G ∈ copland_base_sem p c := by simp

-- The supports preorder for Copland phrases
def Copland.supports_preorder (p : Place) : Preorder Copland :=
  General.supports_preorder (copland_base_sem p)

-- The covers preorder for Copland phrases 
def Copland.covers_preorder (p : Place) : Preorder Copland :=
  General.covers_preorder (copland_base_sem p)

-- These next two lemmas occur as remarks in JDG Fest.
-- They correspond to equation (3) in that paper. 
lemma copland_supports_order_iff (p : Place) (c1 c2 : Copland) :
(Copland.supports_preorder p).le c1 c2 ↔ cop_sem p c2 ≤ cop_sem p c1 := by 
  constructor <;> intro le
  · specialize le ⟦cop_sem p c1⟧
    simp [copland_base_sem] at le
    exact QLPO.le_iff.1 le
  · intros H Hmem
    use ⟦cop_sem p c2⟧
    simp [copland_base_sem] at *
    rw [Hmem]
    rw [QLPO.le_iff]; exact le

lemma copland_covers_order_iff (p : Place) (c1 c2 : Copland) :
(Copland.covers_preorder p).le c1 c2 ↔ cop_sem p c1 ≤ cop_sem p c2 := by
  constructor <;> intro le
  · specialize le ⟦cop_sem p c1⟧
    simp [copland_base_sem] at le
    exact QLPO.le_iff.1 le
  · intros H Hmem
    use ⟦cop_sem p c2⟧
    simp [copland_base_sem] at *
    rw [Hmem, QLPO.le_iff]
    exact le
