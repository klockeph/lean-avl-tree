-- import Batteries.Util.ProofWanted

inductive AVLNode (α : Type) : Nat → Type where
  | nil : AVLNode α 0
  | balanced : α → AVLNode α n → AVLNode α n → AVLNode α (n + 1)
  | leftie : α → AVLNode α (n + 1) → AVLNode α n → AVLNode α (n + 2)
  | rightie : α → AVLNode α n → AVLNode α (n + 1) → AVLNode α (n + 2)
deriving Repr, BEq


set_option eval.type true

#eval AVLNode.balanced 3 AVLNode.nil AVLNode.nil
#eval AVLNode.leftie 3 (AVLNode.balanced 2 AVLNode.nil AVLNode.nil) AVLNode.nil
#eval @AVLNode.leftie Nat 0 3 (AVLNode.balanced 2 AVLNode.nil AVLNode.nil) AVLNode.nil

#eval AVLNode.rightie 3 AVLNode.nil (AVLNode.balanced 2 AVLNode.nil AVLNode.nil)
#eval @AVLNode.rightie Nat 0 3 AVLNode.nil (AVLNode.balanced 2 AVLNode.nil AVLNode.nil)


-- A Context n a means a traversal from a root of an AVL Tree of height n,
-- whose non-nil nodes have values of type a, to some subtree.
-- The index 'n' is the height of the subtree *currently in the hole*.
inductive Context (α : Type) : Nat → Type where
  -- The root context, where every traversal of an AVL tree starts.
  | root : Context α n
  -- A balanced context.
  | BLC : (val : α) → (other : AVLNode α n) → Context α (n + 1) → Context α n
  | BRC : (val : α) → (other : AVLNode α n) → Context α (n + 1) → Context α n
  -- A leftie context, where we've taken the right branch of the subtree.
  | LRC : (val : α) → (left : AVLNode α (n + 1)) → Context α (n + 2) → Context α n
  -- A leftie context, where we've taken the left branch of the subtree.
  | LLC : (val : α) → (right : AVLNode α n) → Context α (n + 2) → Context α (n + 1)
  -- A rightie context, where we've taken the left branch of the subtree.
  | RLC : (val : α) → (right : AVLNode α (n + 1)) → Context α (n + 2) → Context α n
  -- A rightie context, where we've taken the right branch of the subtree.
  | RRC : (val : α) → (left : AVLNode α n) → Context α (n + 2) → Context α (n + 1)
deriving Repr, BEq

structure Zipper (α : Type) : Type where
  n : Nat
  tree : AVLNode α n
  ctx : Context α n
deriving Repr, BEq

#eval (@Zipper.mk Nat 0 (AVLNode.nil) (Context.root))
#eval Zipper.mk 1 (AVLNode.balanced 3 AVLNode.nil AVLNode.nil) (Context.root)
#eval Zipper.mk 0 (AVLNode.nil) (Context.BLC 3 (AVLNode.nil) Context.root)

#print Zipper.mk

def Zipper.go_left {α : Type} (z : Zipper α) : Option (Zipper α) :=
  let {tree, ctx, ..} := z
  match tree with
  | @AVLNode.balanced α n a l r => Zipper.mk n l (Context.BLC a r ctx)
  | @AVLNode.rightie α n a l r => Zipper.mk n l (Context.RLC a r ctx)
  | @AVLNode.leftie α n a l r => Zipper.mk n.succ l (Context.LLC a r ctx)
  | _ => Option.none

#eval (Zipper.mk 1 (AVLNode.balanced 3 AVLNode.nil AVLNode.nil) (Context.root)).go_left
#eval (Zipper.mk 2 (AVLNode.leftie 3 (AVLNode.balanced 2 AVLNode.nil AVLNode.nil) AVLNode.nil) (Context.root)).go_left
#eval (Zipper.mk 2 (@AVLNode.rightie Nat 0 3 AVLNode.nil (AVLNode.balanced 2 AVLNode.nil AVLNode.nil)) (Context.root)).go_left


def Zipper.go_right {α : Type} (z : Zipper α) : Option (Zipper α) :=
  let {tree, ctx, ..} := z
  match tree with
  | @AVLNode.balanced α n a l r => Zipper.mk n r (Context.BRC a l ctx)
  | @AVLNode.leftie α n a l r => Zipper.mk n r (Context.LRC a l ctx)
  | @AVLNode.rightie α n a l r => Zipper.mk n.succ r (Context.RRC a l ctx)
  | _ => none

#eval (Zipper.mk 1 (AVLNode.balanced 3 AVLNode.nil AVLNode.nil) (Context.root)).go_right
#eval (Zipper.mk 2 (AVLNode.leftie 3 (AVLNode.balanced 2 AVLNode.nil AVLNode.nil) AVLNode.nil) (Context.root)).go_right
#eval (Zipper.mk 2 (@AVLNode.rightie Nat 0 3 AVLNode.nil (AVLNode.balanced 2 AVLNode.nil AVLNode.nil)) (Context.root)).go_right


def Zipper.go_up {α : Type} (z : Zipper α) : Option (Zipper α) :=
  let {tree, ctx, ..} := z
  match ctx with
  | @Context.BLC α n x t c => Zipper.mk n.succ (AVLNode.balanced x tree t) c
  | @Context.BRC α n x t c => Zipper.mk n.succ (AVLNode.balanced x t tree) c
  | @Context.LLC α n x t c => Zipper.mk n.succ.succ (AVLNode.leftie x tree t) c
  | @Context.LRC α n x t c => Zipper.mk n.succ.succ (AVLNode.leftie x t tree) c
  | @Context.RLC α n x t c => Zipper.mk n.succ.succ (AVLNode.rightie x tree t) c
  | @Context.RRC α n x t c => Zipper.mk n.succ.succ (AVLNode.rightie x t tree) c
  | _ => none

#eval (Zipper.mk 1 (AVLNode.balanced 3 AVLNode.nil AVLNode.nil) (Context.root)).go_left >>= Zipper.go_up
#eval (Zipper.mk 2 (AVLNode.leftie 3 (AVLNode.balanced 2 AVLNode.nil AVLNode.nil) AVLNode.nil) (Context.root)).go_left >>= Zipper.go_up
#eval (Zipper.mk 2 (@AVLNode.rightie Nat 0 3 AVLNode.nil (AVLNode.balanced 2 AVLNode.nil AVLNode.nil)) (Context.root)).go_left >>= Zipper.go_up

#eval (Zipper.mk 1 (AVLNode.balanced 3 AVLNode.nil AVLNode.nil) (Context.root)).go_right >>= Zipper.go_up
#eval (Zipper.mk 2 (AVLNode.leftie 3 (AVLNode.balanced 2 AVLNode.nil AVLNode.nil) AVLNode.nil) (Context.root)).go_right >>= Zipper.go_up
#eval (Zipper.mk 2 (@AVLNode.rightie Nat 0 3 AVLNode.nil (AVLNode.balanced 2 AVLNode.nil AVLNode.nil)) (Context.root)).go_right >>= Zipper.go_up


theorem go_left_up [BEq α] (z : Zipper α)
  (h1 : some new_z = z.go_left) : new_z.go_up = z :=
  by
  cases z with | mk n tree ctx =>
  dsimp [Zipper.go_left] at h1
  cases tree
  . simp at h1
  all_goals
    injection h1 with h_new_z
    rw [h_new_z]
    dsimp [Zipper.go_up]


theorem go_right_up [BEq α] (z : Zipper α)
  (h1 : some new_z = z.go_right) : new_z.go_up = z := by
  cases z with | mk n tree ctx =>
  dsimp [Zipper.go_right] at h1
  cases tree
  . simp at h1
  all_goals
    injection h1 with h_new_z
    rw [h_new_z]
    dsimp [Zipper.go_up]
