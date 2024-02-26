import Mathlib.Tactic

open Function

-- Surprisingly not in Mathlib
lemma card_eq_of_injective {α β : Type*} [Fintype α] [Fintype β]
{f : α → β} {g : β → α} (hf : Injective f) (hg : Injective g) : 
Fintype.card α = Fintype.card β := 
eq_of_le_of_not_lt (Fintype.card_le_of_injective f hf) 
(not_lt_of_le (Fintype.card_le_of_injective g hg))
