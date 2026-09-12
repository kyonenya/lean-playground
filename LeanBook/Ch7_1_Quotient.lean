import LeanBook.Ch6_3_DecidableOrder

-- ### Equivalence
-- **h : Equivalence r**

example {α : Type}
    (r : α → α → Prop)
    (h : Equivalence r) -- [rは同値関係であるという命題を付け足す]
    : ∀ x, r x x := by
  exact h.refl

-- ### Setoid : Equivalence Relation
-- **sr : Setoid α**

example {α : Type}
    (sr : Setoid α) -- [同値関係としてのr]
    (x y : α)
    : sr.r x y = (x ≈ y) := by
  rfl

-- ### Quotient
-- **A : Quotient sr**

section
  variable {α β : Type} (sr : Setoid α)

  example (A : Quotient sr) : True := by
    induction A using Quotient.inductionOn with
    | h x => trivial

  variable (f : β → α)

-- ### Quotient.mk : make Quotient
-- **Quotient.mk sr : α → A**
  -- α → A ∘ β → α
  #check (Quotient.mk sr ∘ f) -- β → A
end

section
  variable {α β : Type} (sr : Setoid α)
  variable (f : α → β)
    (h : ∀ x y, x ≈ y → f x = f y)

  -- α → β
  #check Quotient.lift f h -- A → β

  example : ∀ x,
      -- F A = f x
      (Quotient.lift f h) (Quotient.mk sr x) = f x := by
    intro x
    dsimp [Quotient.lift, Quotient.mk]
end

section
  variable {α : Type} (sr : Setoid α)
  variable (x y : α) (h : x ≈ y)

  example : Quotient.mk sr x = Quotient.mk sr y := by
    apply Quotient.sound
    exact h

  variable (p q : α)

  example (h : Quotient.mk sr x = Quotient.mk sr y) : x ≈ y := by
    exact Quotient.exact h
end
