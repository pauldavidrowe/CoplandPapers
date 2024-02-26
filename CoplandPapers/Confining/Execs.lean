import CoplandPapers.Confining.Labels

open scoped Classical 

open Label

/- 
  A Component is Relev to an Event if it is the measurer or target of a measurement Event, 
  or something the measurer depends on, or if it is the argument of an adversary Event. 
 -/
inductive Relev {Event : Type} [PartialOrder Event] (l : Event → Label) 
(d : Component → Component → Prop) (c : Component) (e : Event) : Prop 
| meas_m c': l e = msp c c' -> Relev l d c e
| meas_t c': l e = msp c' c -> Relev l d c e
| meas_d c1 c2: l e = msp c1 c2 ∧ d c1 c → Relev l d c e
| adv_c : l e = cor c → Relev l d c e
| adv_r : l e = rep c → Relev l d c e

/-
  Whenever the same Component is Relev to two events and one of those events is an 
  adversary Event, then the eventsare either strictly ordered or equal. 
-/
@[simp]
def AdversaryOrdered {Event : Type} [PartialOrder Event] (ℓ : Event → Label) 
(d : Component → Component → Prop) : Prop :=
∀ e1 e2 c, 
  Relev ℓ d c e1 → Relev ℓ d c e2 → 
  AdvLab (ℓ e1) → (e1 < e2 ∨ e2 < e1 ∨ e2 = e1)

/- 
  This is Definition 4 of Confinig Adversaries. 

  An Exec is a partial order of a Finite set (type) of events that comes equipped with a 
  labeling function, a dependency relation, and a proof that it's adversary ordered. We also 
  attach the dependency relation to the Exec because this is required to determine if it is 
  adversary ordered. Finally, for technical reasons, we assume it's non-empty. 
-/
structure Exec :=
(Evt : Type)
(fin : Fintype Evt)
(poset : PartialOrder Evt)
(l : Evt → Label)
(d : Component → Component → Prop)
(adv_ord : @AdversaryOrdered Evt poset l d)
(ne : Nonempty Evt)

/- 
  Forcing the events to be Nonempty is a little ugly, but it makes it easier to show 
  that < is well_founded due to the use of invFun later which requires it. In any case, 
  empty executions are not interesting for the application. 
-/
instance Exec.nonempty_evt (E : Exec) : Nonempty E.Evt := E.ne

/-
  The next few definitions let Lean know that E.Evt is a partial order, a
  Preorder, a Finite type, and that < is a well-founded order. By declaring them
  as instances, Lean automatically finds these facts when it needs them. 
-/
@[instance]
def Exec.Evt.PartialOrder (E : Exec) : PartialOrder E.Evt := E.poset 

@[instance]
def Exec.Evt.Preorder (E : Exec): Preorder E.Evt := PartialOrder.toPreorder 

@[instance]
def Exec.Evt.Fintype (E : Exec) : Fintype E.Evt := E.fin 

@[instance]
def Exec.Evt.Finite (E : Exec) : Finite E.Evt := Finite.of_fintype E.Evt 

@[instance]
def Exec.Evt.hasWellFounded (E : Exec) : WellFoundedRelation E.Evt := 
{ rel := LT.lt 
  wf := wellFounded_lt }

variable {E : Exec} {c : Component} {e : E.Evt}

/-
  The next few lines define subsets of E.Evt satisfying certain properties, and
  prove that each such subset is Finite. Finiteness of ard (short for "adversary 
  relevant down") is necessary for proving Lemma 1 below, and finiteness of ard
  follows from finiteness of the sets being intersected in its definition. 
-/
@[simp]
def AdvEvt (e : E.Evt) := AdvLab (E.l e)

lemma adv_evt_label : 
(AdvEvt e) ↔ ∃ c, (E.l e = cor c) ∨ (E.l e = rep c) := by 
  constructor
  · simp; intro h 
    rw [adv_lab_adv_lab'] at h; exact h
  · simp; intro c h 
    rw [adv_lab_adv_lab']; simp; use c

-- The set of all adversary events of E. 
@[simp]
def adv_evts (E : Exec) := { e : E.Evt | AdvEvt e }

lemma fin_adv_evts (E : Exec) : (adv_evts E).Finite := 
  (adv_evts E).toFinite

@[simp]
def MeasEvt (e : E.Evt) := MSLab (E.l e)

-- The set of all measurement events of E. 
@[simp]
def MeasEvts (E : Exec) :=
{ e : E.Evt | MeasEvt e }

lemma fin_meas_evts (E : Exec) : (MeasEvts E).Finite := 
(MeasEvts E).toFinite

inductive Relevant (c : Component) (e : E.Evt) : Prop 
| meas_m c' : E.l e = msp c c' → Relevant c e
| meas_t c' : E.l e = msp c' c → Relevant c e
| meas_d c1 c2 : E.l e = msp c1 c2 ∧ E.d c1 c → Relevant c e
| adv_c : E.l e = cor c → Relevant c e
| adv_r : E.l e = rep c → Relevant c e

lemma rel_relevant (c : Component) (e : E.Evt) :
Relev E.l E.d c e ↔ Relevant c e := by 
  constructor <;> intro h
  rcases h with hm | ht | hd | hc | hr
  · apply Relevant.meas_m; assumption
  · apply Relevant.meas_t; assumption
  · apply Relevant.meas_d; tauto
  · apply Relevant.adv_c; assumption
  · apply Relevant.adv_r; assumption
  rcases h with hm | ht | hd | hc | hr
  · apply Relev.meas_m; assumption
  · apply Relev.meas_t; assumption
  · apply Relev.meas_d; tauto
  · apply Relev.adv_c; assumption
  · apply Relev.adv_r; assumption

lemma meas_cor_rep_of_relevant {E : Exec} {e : E.Evt} {c : Component} 
(r : Relevant c e) : (∃ c1 c2, E.l e = msp c1 c2) ∨ (E.l e = cor c) ∨ 
(E.l e = rep c) := by 
  rw [←rel_relevant] at r
  cases r
  case meas_m c1 lab
  · left; use c, c1, lab
  case meas_t c1 lab 
  · left; use c1, c, lab
  case meas_d c1 c2 lab
  · left; use c1, c2, lab.1
  case adv_c lab
  · right; left; exact lab
  case adv_r lab
  · right; right; exact lab

lemma components_of_adv_lab 
(h1 : Relevant c e) (h2 : AdvLab' (E.l e)) :
E.l e = cor c ∨ E.l e = rep c := by 
  obtain ⟨c1, h2⟩ := h2 
  cases h2 with 
  | inl h2 => 
    left; cases h1 with
    | meas_m _ h3 => rw [h2] at h3; cases h3
    | meas_t _ h3 => rw [h2] at h3; cases h3
    | meas_d _ _ h3 => rw [h2] at h3; cases h3.1
    | adv_c h3 => exact h3
    | adv_r h3 => rw [h2] at h3; cases h3
  | inr h2 => 
    right; cases h1 with 
    | meas_m _ h3 => rw [h2] at h3; cases h3
    | meas_t _ h3 => rw [h2] at h3; cases h3
    | meas_d _ _ h3 => rw [h2] at h3; cases h3.1
    | adv_c h3 => rw [h2] at h3; cases h3
    | adv_r h3 => exact h3

-- The set of all events of E to which c is Relevant
@[simp]
def restrict (E : Exec) (c : Component) := { e : E.Evt | Relevant c e}

lemma fin_restrict (E : Exec) (c : Component) : (restrict E c).Finite :=
(restrict E c).toFinite

-- The set of all events strictly below a given Event e. 
@[simp]
def downset (e : E.Evt) := { e' : E.Evt | e' < e }

lemma fin_downset (e: E.Evt) : (downset e).Finite := (downset e).toFinite

-- The set of all adversary events for c that are below a given Event e. 
@[simp]
def adv_relevant_down (c : Component) (e : E.Evt) :=
adv_evts E ∩ downset e ∩ restrict E c  

lemma fin_adv_rel_down (c : Component) (e : E.Evt) :
(adv_relevant_down c e).Finite :=
by 
  simp at *; apply Set.Finite.inter_of_right;
  apply fin_restrict

lemma inv_relevant (c : Component) (e : E.Evt) :
Relevant c e → 
  E.l e = cor c ∨ 
  E.l e = rep c ∨ 
  (∃ c', E.l e = msp c c') ∨ 
  (∃ c', E.l e = msp c' c) ∨ 
  (∃ c' c'', E.l e = msp c' c'' ∧ E.d c' c) := by 
  intro h 
  cases h with 
  | meas_m c1 h1 => right; right; left; use c1
  | meas_t c1 h1 => right; right; right; left; use c1
  | meas_d c1 c2 h1 => right; right; right; right; use c1, c2
  | adv_c h1 => left; exact h1
  | adv_r h1 => right; left; exact h1

lemma inv_relevant_simp (c : Component) (e : E.Evt) :
Relevant c e → 
  E.l e = cor c ∨ 
  E.l e = rep c ∨ 
  (∃ c1 c2, E.l e  = msp c1 c2) := by 
  intro h
  cases h with
  | meas_m c1 h1 => right; right; use c, c1
  | meas_t c1 h1 => right; right; use c1, c
  | meas_d c1 c2 h1 => right; right; use c1, c2; exact h1.1 
  | adv_c h1 => left; exact h1
  | adv_r h1 => right; left; exact h1 

def D (E : Exec) (c o : Component) :=
∃ e m, E.l e = msp m o ∧ (c = m ∨ E.d m c)
