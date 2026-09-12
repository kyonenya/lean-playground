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
  -- (α → A) ∘ (β → α)
  #check (Quotient.mk sr ∘ f) -- β → A
end

section
  variable {α β : Type} (sr : Setoid α)
  variable (f : α → β)
  -- [Quotient.liftするときは毎回、異なる代表元を選んでも関数結果が同じになることを証明しなければならない]
 variable (h : ∀ x y, x ≈ y → f x = f y)

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
  variable (a₁ a₂ : α) (h : a₁ ≈ a₂)

  /-- (α → A) a₁ = (α → A) a₂ -/
  example : Quotient.mk sr a₁ = Quotient.mk sr a₂ := by -- A₁ = A₂
  -- [元の世界で同値な二つの元は、商の世界では同じ要素に潰れる]
    apply Quotient.sound -- a₁ ≈ a₂ → A₁ = A₂
    exact h

  variable (p q : α)

  example (h : Quotient.mk sr x = Quotient.mk sr y) : x ≈ y := by
    -- [商の世界で同じ要素に潰れる二つの元は、元の世界でも同値]
    exact Quotient.exact h
end
