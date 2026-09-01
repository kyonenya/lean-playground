import LeanBook.Ch6_3_DecidableOrder

-- ## Setoid

/-- 2 次元平面 -/
structure Point where
  x : Int
  y : Int

#check { x := 1, y := 2 : Point }

-- .mkという名前でコンストラクタを呼べる
#check Point.mk

#check Point.mk 1 2

#eval
  let p : Point := { x := 1, y := 2 }
  -- フィールド記法
  p.x

-- ### 同値関係 Equivalence

/-
structure Equivalence {α : Sort u} (r : α → α → Prop) : Prop where
  refl : ∀ x, r x x
  symm : ∀ {x y}, r x y → r y x
  trans : ∀ {x y z}, r x y → r y z → r x z
-/

/-- 同値性から反射的であることを導く -/
example {α : Type} (r : α → α → Prop) (h : Equivalence r) : ∀ x, r x x := by
  exact h.refl

/-- どんな型αに対しても、r x y := x = yとして二項関係rを定義すると必ず同値関係になる -/
example {α : Type} : Equivalence (fun x y : α => x = y) := by
  -- Equivalence を refl, symm, trans に分解
  constructor
  case refl =>
    intro x
    rfl
  case symm =>
    intro x y h
    rw [h]
  case trans =>
    intro x y z hxy hyz
    rw [hxy, hyz]

-- ### Setoid: 二項関係 r と、それが同値関係であることの証明をまとめたもの

/-
class Setoid (α : Sort u) where
  -- 二項関係 r : α → α → Prop
  r : α → α → Prop
  -- 二項関係 r は同値関係である
  iseqv : Equivalence r
-/

-- 同値関係を ≈ (\approx) という記号で表せる
example {α : Type} (sr : Setoid α) (x y : α) :
  sr.r x y = (x ≈ y) := by
  rfl

-- ### 商 Quotient と同値類 equivalence class

-- 同値類は Quotient.mk で取る
section
  variable {I : Type} (mergeRel : Setoid I)
  #check (Quotient.mk mergeRel : I → Quotient mergeRel)
end

-- 代表元は Quotient.inductionOn で取る
-- 商そのもの R ではなく元の型 i₁ に話を移せる
section

  variable {I : Type} (mergeRel : Setoid I)

  example (world : Quotient mergeRel) : True := by
    induction world using Quotient.inductionOn with
    | h i₁ =>
      guard_hyp i₁ : I
      trivial

end

-- ある型 β から商 Quotient sr への関数を得るには、たとえば自然な関数 α → Quotient sr と関数 β → α を合成すれば実現できます
section
  -- 商への関数を作る
  variable {T I : Type} (mergeRel : Setoid I)

  variable (instanceAt : T → I)

  #check (
    Quotient.mk mergeRel ∘ instanceAt :
      T → Quotient mergeRel
  )
end

-- Quotient.lift：関数を商へ持ち上げる操作

-- もし関数 f : α → β が同値類 Quotient sr のどの要素に対しても同じ値を返すならば、f の定義域を Quotient sr に持ち上げて、Quotient sr → βという関数が得られます。この操作はQuotient.liftで実現できます
section
  -- 商からの関数を作る：jLevel を求める関数

  variable {I J : Type} (mergeRel : Setoid I)
  variable
    (toJLevel : I → J)
    -- [同じ世界のインスタンスなら、どちらを代表元にしても同じjレベルを得る]
    (h : ∀ i₁ i₂, i₁ ≈ i₂ → toJLevel i₁ = toJLevel i₂)

  #check (Quotient.lift toJLevel h : Quotient mergeRel → J) -- W → J

  -- Quotient.lift は元の関数の値を変えない
  example :
      ∀ i₁,
        (Quotient.lift toJLevel h) (Quotient.mk mergeRel i₁)
          = toJLevel i₁ := by
    intro i₁
    rfl
end

/- Quotient.sound 同値なら商へ送っても等しい -/
section
  -- [二つのインスタンスが同一世界にマージされるなら、それぞれから作った世界個体は等しい]
  variable {I : Type} (mr : Setoid I)
  variable (i₁ i₂ : I) (h : i₁ ≈ i₂)

  example : Quotient.mk mr i₁ = Quotient.mk mr i₂ := by
    exact Quotient.sound h
end

/- Quotient.exact 商に送って等しいなら同値 -/
section
  -- [二つのインスタンスから作った世界個体が同じなら、その二つのインスタンスはマージ関係にある]
  variable {I : Type} (mr : Setoid I)
  variable (i₁ i₂ : I)

  example (h : Quotient.mk mr i₁ = Quotient.mk mr i₂) : i₁ ≈ i₂ := by
    exact Quotient.exact h
end

/-- J 上の二項関係 jRel : I → I → Prop を、関数 toJ : I → J を通じて I 上の二項関係に引き戻したもの
関係を受け取って新しい関係を返す関数
-/
private def Rel.comap {I J : Type}
    (toJ : I → J)
    (jRel : J → J → Prop)
    : I → I → Prop :=
  fun (i₁ i₂) => jRel (toJ i₁) (toJ i₂)

/-- J 上の同値関係 jRel : Setoid J と関数 toJ : I → J があるなら、
I 上の二項関係 Rel.comap も同値関係になる -/
private def Setoid.comap {I J : Type}
    (toJ : I → J)
    (jRel : Setoid J)
    : Setoid I where
  r := Rel.comap toJ (· ≈ ·)
  iseqv := by
    constructor <;> dsimp [Rel.comap]
    case refl =>
      intro i₁
      apply jRel.iseqv.refl
    case symm =>
      intro i₁ i₂
      apply jRel.iseqv.symm
    case trans =>
      intro i₁ i₂ i₃
      apply jRel.iseqv.trans

-- ---
