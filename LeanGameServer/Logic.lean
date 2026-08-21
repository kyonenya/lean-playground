example (P : Prop)
    (todo_list : P) :
    P := by
  exact todo_list

example (P S : Prop)
    (p : P)
    (s : S) :
    (P ∧ S) := by
  exact And.intro p s
