inductive MyNat where -- 帰納的定義
  | zero
  | succ (n : MyNat)

def MyNat.ofNat (n : Nat) : MyNat :=
  match n with
  | 0 => MyNat.zero
  | n + 1 => MyNat.succ (MyNat.ofNat n)

#check MyNat.zero -- MyNat
#check MyNat.succ -- MyNat → MyNat

#eval MyNat.succ .zero -- succ(0)
#check MyNat.succ .zero -- MyNat

def MyNat.one := MyNat.succ .zero
def MyNat.two := MyNat.succ .one

def MyNat.add (m n : MyNat) : MyNat :=
  match n with
  | zero => m
  -- この n は 別スコープの変数、k でもいい
  | succ n => succ (add m n) -- succ を外出し

#check MyNat.add .one .one = .two

set_option pp.fieldNotation.generalized false

-- #reduce：式を最も基本的な形に戻す、還元する
#reduce MyNat.add .one .one -- succ (succ 0)
#reduce MyNat.two -- succ (succ 0)

example : MyNat.add .one .one = .two := by
  rfl
