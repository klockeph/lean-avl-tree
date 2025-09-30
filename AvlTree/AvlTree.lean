import Aesop

/-
A very WIP implementation of AVL Trees with dependent Types in Lean4.
I used https://fedelebron.com/compile-time-invariants-in-haskell as an inspiration.
-/
set_option eval.type true

inductive AVLNode (α : Type) : Nat → Type where
  | nil : AVLNode α 0
  | balanced : α → AVLNode α n → AVLNode α n → AVLNode α (n + 1)
  | leftie : α → AVLNode α (n + 1) → AVLNode α n → AVLNode α (n + 2)
  | rightie : α → AVLNode α n → AVLNode α (n + 1) → AVLNode α (n + 2)
deriving Repr, BEq

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
  | BLC : (val : α) → (right : AVLNode α n) → Context α (n + 1) → Context α n
  | BRC : (val : α) → (left : AVLNode α n) → Context α (n + 1) → Context α n
  -- A leftie context, where we've taken the left branch of the subtree.
  | LLC : (val : α) → (right : AVLNode α n) → Context α (n + 2) → Context α (n + 1)
  -- A leftie context, where we've taken the right branch of the subtree.
  | LRC : (val : α) → (left : AVLNode α (n + 1)) → Context α (n + 2) → Context α n
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


def AVLNode.node_count : (AVLNode α n) → Nat
  | .nil => 1
  | .balanced _ l r => 1 + l.node_count + r.node_count
  | .leftie _ l r => 1 + l.node_count + r.node_count
  | .rightie _ l r => 1 + l.node_count + r.node_count


theorem avl_node_count_gt_0 (t : AVLNode α n) : t.node_count > 0 := by
  induction t
  simp_all[AVLNode.node_count]
  all_goals
  rename_i _ _ t1 t2 ih1 ih2
  simp_all[AVLNode.node_count]
  rw [Nat.add_assoc]
  rw [Nat.add_comm]
  simp only [Nat.zero_lt_succ]


theorem go_left_count_lt (z : Zipper α)
  (h : some lz = z.go_left)
  : lz.tree.node_count < z.tree.node_count := by
  cases z with | mk n tree ctx
  cases tree
  all_goals
  simp_all[Zipper.go_left]
  all_goals
  rename_i l r
  rw[h]
  simp_all[AVLNode.node_count]
  rw [Nat.add_comm 1, Nat.add_assoc]
  apply Nat.lt_add_of_pos_right
  rw [Nat.add_comm]
  simp only [Nat.zero_lt_succ]


theorem go_right_count_lt (z : Zipper α)
  (h : some rz = z.go_right)
  : rz.tree.node_count < z.tree.node_count := by
  cases z with | mk n tree ctx
  cases tree
  all_goals
  simp_all[Zipper.go_right]
  all_goals
  rename_i l r
  rw[h]
  simp_all[AVLNode.node_count]
  rw [Nat.add_comm]
  simp only [Nat.zero_lt_succ]


def Zipper.value? : (z : Zipper α) → Option α
  | {tree, ..} => match tree with
    | .balanced x _ _ => x
    | .rightie x _ _ => x
    | .leftie x _ _ => x
    | .nil => none


-- Zips to the element or to the Nil node where it should be inserted
def Zipper.zip_to [Ord α] (a : α) (z : Zipper α) : Zipper α :=
  if let some x := z.value? then
    match compare a x with
    | Ordering.lt => match h: z.go_left with
      | none => z
      | some lz =>
        have : lz.tree.node_count < z.tree.node_count := by simp_all[go_left_count_lt]
        lz.zip_to a
    | Ordering.gt => match h: z.go_right with
      | none => z
      | some rz =>
        have : rz.tree.node_count < z.tree.node_count := by simp_all[go_right_count_lt]
        rz.zip_to a
    | Ordering.eq => z
  else z
termination_by z.tree.node_count


structure AVLTree α where
  n : Nat
  node: (AVLNode α n)

def AVLTree.unzip (t : AVLTree α) : Zipper α :=
  Zipper.mk t.n t.node Context.root

def Context.node_count : (c: Context α n) → Nat
  | .root => 0
  | .BLC _ a b => a.node_count + b.node_count
  | .BRC _ a b => a.node_count + b.node_count
  | .LLC _ a b => a.node_count + b.node_count
  | .LRC _ a b => a.node_count + b.node_count
  | .RLC _ a b => a.node_count + b.node_count
  | .RRC _ a b => a.node_count + b.node_count

theorem zipper_ctx_nil_go_up (z : Zipper α) (h: z.ctx = Context.root)
  : z.go_up = none := by
  simp_all[Zipper.go_up]

theorem zipper_go_up_ctx_node_count_lt (z : Zipper α) (h : some upper = z.go_up)
  : upper.ctx.node_count < z.ctx.node_count := by
  obtain ⟨n, tree, ctx⟩ := z
  unfold Zipper.go_up at h
  cases ctx
  . simp_all
  all_goals
  rename_i val t a
  simp_all[Context.node_count]
  rw[h]
  simp_all[avl_node_count_gt_0]


def Zipper.zip_up : (z: Zipper α) → AVLTree α
  | Zipper.mk n t .root => (AVLTree.mk n t)
  | some_z => match c: some_z.go_up with
    | some upper =>
      have : upper.ctx.node_count < some_z.ctx.node_count := by simp_all[zipper_go_up_ctx_node_count_lt]
      upper.zip_up
    | none => (AVLTree.mk 0 .nil) -- it would be nicer to panic but AVLTree is not inhibited
termination_by z => z.ctx.node_count

/-
TODO: We define this later, once we have rotations

def AVLTree.insert [Ord α] (tree: AVLTree α) (a: α) : AVLTree α :=
  match tree.unzip.zip_to a with
  | Zipper n .nil ctx -> insert_and_fix (.balanced x .nil .nil) ctx
  | _ -> tree

-/











-- Theorems that were not required but too nice to throw away...
-- And their accompanying functions :)

def AVLNode.left_child : (AVLNode α n) → Option ((m : Nat) × AVLNode α m)
  | @AVLNode.balanced _ m _ l _ => some ⟨m, l⟩
  | @AVLNode.leftie _ m _ l _ => some ⟨m + 1, l⟩
  | @AVLNode.rightie _ m _ l _ => some ⟨m, l⟩
  | .nil => none

def AVLNode.right_child : (AVLNode α n) → Option ((m : Nat) × AVLNode α m)
  | @AVLNode.balanced _ m _ _ r => some ⟨m, r⟩
  | @AVLNode.leftie _ m _ _ r => some ⟨m, r⟩
  | @AVLNode.rightie _ m _ _ r => some ⟨m + 1, r⟩
  | .nil => none

theorem zero_lt_node_count (t : AVLNode α n) : 0 < t.node_count := by
  induction t
  . simp[AVLNode.node_count]
  all_goals
  rename_i a r l l_ih rih
  simp[AVLNode.node_count, Nat.add_pos_iff_pos_or_pos]

theorem left_child_smaller (t : AVLNode α n) {m : Nat} {child : AVLNode α m}
  (h : some ⟨m, child⟩ = t.left_child) : child.node_count < t.node_count := by
  dsimp[AVLNode.left_child] at h
  cases t
  . simp_all
  all_goals
  rename_i l r
  injection h with h_child
  cases h_child
  simp_all[AVLNode.node_count]
  rw [Nat.add_comm 1, Nat.add_assoc]
  apply Nat.lt_add_of_pos_right
  rw [Nat.add_comm]
  simp only [Nat.zero_lt_succ]

theorem right_child_smaller (t : AVLNode α n) {m : Nat} {child : AVLNode α m}
  (h : some ⟨m, child⟩ = t.right_child) : child.node_count < t.node_count := by
  dsimp[AVLNode.right_child] at h
  cases t
  . simp_all
  all_goals
  rename_i l r
  injection h with h_child
  cases h_child
  simp_all[AVLNode.node_count]
  rw [Nat.add_comm]
  simp only [Nat.zero_lt_succ]

theorem go_left_left_n (z : Zipper α)
  (h₁: some new_z = z.go_left) (h₂ : some lcp = z.tree.left_child) :
   lcp.1 = new_z.n :=
  by
    unfold Zipper.go_left at h₁
    cases z with | mk n tree ctx
    simp_all
    cases tree
    . simp_all
    all_goals
    rename_i n a t₁ t₂
    simp_all
    injection h₂ with new_z
    rw[new_z]

theorem go_left_left_child [BEq α] (z : Zipper α) (new_z : Zipper α) (lcp : (m : Nat) × AVLNode α m)
  (h₁: some new_z = z.go_left) (h₂ : some lcp = z.tree.left_child) (h₃ : lcp.fst = new_z.n)
  : (h₃ ▸ lcp.2 = new_z.tree) := by
    unfold Zipper.go_left at h₁
    cases z with | mk n tree ctx
    cases tree
    . simp_all
    all_goals
    cases h₁; cases h₂; cases h₃
    simp_all

theorem go_right_right_n (z : Zipper α)
  (h₁: some new_z = z.go_right) (h₂ : some lcp = z.tree.right_child) :
   lcp.1 = new_z.n :=
  by
    unfold Zipper.go_right at h₁
    cases z with | mk n tree ctx
    simp_all
    cases tree
    . simp_all
    all_goals
    rename_i n a t₁ t₂
    simp_all
    injection h₂ with new_z
    rw[new_z]

theorem go_right_right_child [BEq α] (z : Zipper α) (new_z : Zipper α) (lcp : (m : Nat) × AVLNode α m)
  (h₁: some new_z = z.go_right) (h₂ : some lcp = z.tree.right_child) (h₃ : lcp.fst = new_z.n)
  : (h₃ ▸ lcp.2 = new_z.tree) := by
    unfold Zipper.go_right at h₁
    cases z with | mk n tree ctx
    cases tree
    . simp_all
    all_goals
    cases h₁; cases h₂; cases h₃
    simp_all
