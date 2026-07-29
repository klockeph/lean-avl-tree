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
#eval @AVLNode.rightie Nat 0 3 AVLNode.nil (@AVLNode.balanced Nat 0 2 AVLNode.nil AVLNode.nil)

-- A Context n a means a traversal from a root of an AVL Tree of height n,
-- whose non-nil nodes have values of type α, to some subtree.
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
  | _ => none

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


-- If we first go left and then go up, we end up back where we started.
theorem go_left_up (z : Zipper α)
  (h1 : some new_z = z.go_left) : new_z.go_up = z :=
  by
  obtain ⟨n, tree, ctx⟩ := z
  dsimp [Zipper.go_left] at h1
  cases tree
  . simp at h1
  all_goals
    injection h1 with h_new_z
    rw [h_new_z]
    dsimp [Zipper.go_up]

-- If we first go right and then go up, we end up back where we started.
theorem go_right_up (z : Zipper α)
  (h1 : some new_z = z.go_right) : new_z.go_up = z := by
  obtain ⟨n, tree, ctx⟩ := z
  dsimp [Zipper.go_right] at h1
  cases tree
  . simp at h1
  all_goals
    injection h1 with h_new_z
    rw [h_new_z]
    dsimp [Zipper.go_up]

theorem go_left_n_lt (z : Zipper α)
  (h : some lz = z.go_left)
  : lz.n < z.n := by
  obtain ⟨n, tree, ctx⟩ := z
  cases tree
  all_goals
  simp_all[Zipper.go_left]

theorem go_right_n_lt (z : Zipper α)
  (h : some rz = z.go_right)
  : rz.n < z.n := by
  obtain ⟨n, tree, ctx⟩ := z
  cases tree
  all_goals
  simp_all[Zipper.go_right]

def Zipper.value? : (z : Zipper α) → Option α
  | {tree, ..} => match tree with
    | .balanced x _ _ | .rightie x _ _ | .leftie x _ _ => x
    | .nil => none

-- Zips to the element or to the Nil node where it should be inserted
def Zipper.zip_to [Ord α] (a : α) (z : Zipper α) : Zipper α :=
  if let some x := z.value? then
    match compare a x with
    | Ordering.lt => match h: z.go_left with
      | none => z
      | some lz =>
        have : lz.n < z.n := by simp_all[go_left_n_lt]
        lz.zip_to a
    | Ordering.gt => match h: z.go_right with
      | none => z
      | some rz =>
        have : rz.n < z.n := by simp_all[go_right_n_lt]
        rz.zip_to a
    | Ordering.eq => z
  else z
termination_by z.n


structure AVLTree α where
  n : Nat
  node: (AVLNode α n)

-- Useful if we want to panic! from a function that returns AVLTree.
instance : Inhabited (AVLTree α) where
  default := AVLTree.mk 0 .nil

-- A constructor for convenience
def AVLTree.from_node {α n} : (node: AVLNode α n) → AVLTree α := AVLTree.mk n

def AVLTree.unzip (t : AVLTree α) : Zipper α :=
  Zipper.mk t.n t.node Context.root

def Context.depth : (c: Context α n) → Nat
  | .root => 0
  | .BLC _ _ c => 1 + c.depth
  | .BRC _ _ c => 1 + c.depth
  | .LLC _ _ c => 1 + c.depth
  | .LRC _ _ c => 1 + c.depth
  | .RLC _ _ c => 1 + c.depth
  | .RRC _ _ c => 1 + c.depth

theorem zipper_go_up_ctx_depth_lt (z : Zipper α) (h : some upper = z.go_up)
  : upper.ctx.depth < z.ctx.depth := by
  obtain ⟨n, tree, ctx⟩ := z
  unfold Zipper.go_up at h
  cases ctx
  · simp_all
  all_goals
    rename_i val t a
    simp_all [Context.depth]
    rw[h]
    simp_all

def Zipper.zip_up (z : Zipper α) : AVLTree α :=
    match c: z.go_up with
    | some upper =>
      have : upper.ctx.depth < z.ctx.depth := by simp_all[zipper_go_up_ctx_depth_lt]
      upper.zip_up
    | none => AVLTree.mk z.n z.tree
termination_by z.ctx.depth

/-
`node` is one level taller than what `ctx` expects (height n+1 in a height-n hole).
We walk up the context rebalancing as needed. Cases fall into three groups:

  (1) Local fix — the growth resolves an existing imbalance; height stops increasing.
  (2) Propagate — a balanced node becomes tilted; height still grew, so recurse up.
  (3) Rotate — an already-tilted node reaches a height diff of 2; rotate and stop.
-/
def insert_and_fix (node : AVLNode α n.succ) (ctx: Context α n) : AVLTree α :=
  match ctx with
  -- Base case: the tree was empty; the inserted node becomes the root.
  | .root => AVLTree.from_node node

  -- (1) Was a leftie; inserted into the *shorter* right child, which now matches the
  --     left. The leftie becomes balanced; overall height is unchanged.
  | .LRC val l ctx => Zipper.mk n.succ.succ (.balanced val l node) ctx |>.zip_up

  -- (1) Symmetric: was a rightie; inserted into the shorter left child.
  | .RLC val r ctx => Zipper.mk n.succ.succ (.balanced val node r) ctx |>.zip_up

  -- (2) Was balanced; inserted into left child, which is now taller → becomes a leftie.
  --     Height grew by one, so keep fixing upward.
  | .BLC val r ctx => insert_and_fix (.leftie val node r) ctx

  -- (2) Symmetric: was balanced; inserted into right child → becomes a rightie.
  | .BRC val l ctx => insert_and_fix (.rightie val l node) ctx

  -- (3) Was a leftie (left already taller); inserted into the *left* child again.
  --     Height diff is now 2 — rebalance with one or two rotations.
  | @Context.LLC α nc val r ctx => match node with

    -- Left-left: single right rotation.
    --       P (leftie)         L (balanced)
    --      / \                / \
    --     L   r      →      LL   P
    --    / \                    / \
    --   LL  LR                LR   r
    | .leftie nval ll lr =>
      Zipper.mk nc.succ.succ (.balanced nval ll (.balanced val lr r)) ctx |>.zip_up

    -- Left-right: double rotation (left on L, then right on P).
    -- The three sub-cases distribute LR's children depending on LR's own balance.
    --       P (leftie)              LR (balanced)
    --      / \                     /              \
    --     L   r      →           L                 P
    --    / \                    / \               / \
    --   LL  LR                LL  t1            t2   r
    --      / \
    --     t1  t2
    | .rightie nval ll lr =>
      -- Matching on `nc` (and ignoring it with `_`) is required for the elaborator
      -- to assign the correct index (nc + 2) to the result type.
      Zipper.mk nc.succ.succ (match nc, lr with
        | _, .leftie x t1 t2 => .balanced x (.balanced nval ll t1) (.rightie val t2 r)
        | _, .rightie x t1 t2 => .balanced x (.leftie nval ll t1) (.balanced val t2 r)
        | _, .balanced x t1 t2 => .balanced x (.balanced nval ll t1) (.balanced val t2 r)
        : AVLNode α (nc + 2)
      ) ctx |>.zip_up

    -- Likely unreachable via AVLTree.insert: all recursive calls pass leftie/rightie nodes,
    -- and the initial balanced node (height 1) cannot reach LLC. Reachable if called directly.
    -- Required by exhaustiveness.
    --
    -- We cannot represent a height-diff-2 node in AVLNode, so we must reorganize the five
    -- pieces into a valid shape before propagating up. A right rotation gives:
    --   rightie nval ll (leftie val lr r)
    -- The result is a valid AVL node but still one taller than the parent context expects,
    -- so we recurse. Note the result is a *rightie* (not leftie): after rotation, nval's
    -- right subtree (which absorbs val and lr) is taller than its left (ll).
    | .balanced nval ll lr =>
      insert_and_fix (.rightie nval ll (.leftie val lr r)) ctx

  -- (3) Symmetric: was a rightie; inserted into the *right* child.
  | @Context.RRC α nc val l ctx => match node with

    -- Right-right: single left rotation.
    | .rightie nval rl rr =>
      Zipper.mk nc.succ.succ (.balanced nval (.balanced val l rl) rr) ctx |>.zip_up

    -- Right-left: double rotation (right on R, then left on P).
    | .leftie nval rl rr =>
      Zipper.mk nc.succ.succ (match nc, rl with
        | _, .rightie x t1 t2 => .balanced x (.leftie val l t1) (.balanced nval t2 rr)
        | _, .leftie x t1 t2 => .balanced x (.balanced val l t1) (.rightie nval t2 rr)
        | _, .balanced x t1 t2 => .balanced x (.balanced val l t1) (.balanced nval t2 rr)
        : AVLNode α (nc + 2)
      ) ctx |>.zip_up

    -- Right-balanced: symmetric to left-balanced.
    | .balanced nval rl rr =>
      insert_and_fix (.leftie nval (.rightie val l rl) rr) ctx


def AVLTree.insert [Ord α] (tree: AVLTree α) (a: α) : AVLTree α :=
  match tree.unzip.zip_to a with
  | (Zipper.mk 0 .nil ctx) => insert_and_fix (.balanced a .nil .nil) ctx
  | _ => tree


-- Trying out some different rotations
-- Left-left:
#eval AVLTree.mk 0 .nil |>.insert 3
#eval AVLTree.mk 0 .nil |>.insert 3 |>.insert 2
#eval AVLTree.mk 0 .nil |>.insert 3 |>.insert 2 |>.insert 1

-- Right-right:
#eval AVLTree.mk 0 .nil |>.insert 3
#eval AVLTree.mk 0 .nil |>.insert 3 |>.insert 4
#eval AVLTree.mk 0 .nil |>.insert 3 |>.insert 4 |>.insert 5

-- Left-right:
#eval AVLTree.mk 0 .nil |>.insert 3
#eval AVLTree.mk 0 .nil |>.insert 3 |>.insert 1
#eval AVLTree.mk 0 .nil |>.insert 3 |>.insert 1 |>.insert 2

-- Right-left:
#eval AVLTree.mk 0 .nil |>.insert 3
#eval AVLTree.mk 0 .nil |>.insert 3 |>.insert 5
#eval AVLTree.mk 0 .nil |>.insert 3 |>.insert 5 |>.insert 4

-- ^^^ The above basically is a (insert-only) definition of a AVL Tree. ^^^

-- Zip to leftmost child of current subtree.
def Zipper.zip_to_smallest (z : Zipper α) : Zipper α :=
  match h : z.go_left with
  | none => z
  | some lz =>
    match lz.n with
    | 0     => z              -- left child is nil; z is already the minimum
    | _ + 1 =>
      have : lz.n < z.n := by simp_all [go_left_n_lt]
      lz.zip_to_smallest
termination_by z.n

-- Go up until we find an ancestor node for which we are in the left subtree.
-- Returns that ancestor (not the node we started from).
def Zipper.zip_to_first_left_parent (z : Zipper α) : Option (Zipper α) :=
  match z.n, z.ctx with
  | _, .root             => none
  -- We came from the left, so return the parent (which is the first left parent).
  | _, .BLC _ _ _ | _, .RLC _ _ _ | _, .LLC _ _ _ => z.go_up
  -- We came from the right, so keep searching
  | _, _ =>
    match h : z.go_up with
    | none       => none
    | some upper =>
      have : upper.ctx.depth < z.ctx.depth := zipper_go_up_ctx_depth_lt z h.symm
      upper.zip_to_first_left_parent
termination_by z.ctx.depth

def Zipper.zip_to_successor (z : Zipper α) : Option (Zipper α) :=
  match z.go_right with
  | some rz => some rz.zip_to_smallest  -- in-order successor = leftmost in right subtree
  | none    => z.zip_to_first_left_parent

-- This is called 'fixContext' in the original blog post
def Context.replace_val [BEq α] (old new_val : α) : Context α n → Context α n
  | .root => .root
  | .BLC v r c => .BLC (if v == old then new_val else v) r (c.replace_val old new_val)
  | .BRC v l c => .BRC (if v == old then new_val else v) l (c.replace_val old new_val)
  | .LLC v r c => .LLC (if v == old then new_val else v) r (c.replace_val old new_val)
  | .LRC v l c => .LRC (if v == old then new_val else v) l (c.replace_val old new_val)
  | .RLC v r c => .RLC (if v == old then new_val else v) r (c.replace_val old new_val)
  | .RRC v l c => .RRC (if v == old then new_val else v) l (c.replace_val old new_val)

def rebalance (node : AVLNode α n) (ctx : Context α n.succ) : AVLTree α :=
  match ctx with
  | .root => AVLTree.from_node node

  -- Was balanced, deleted from left → becomes rightie (height unchanged → stop)
  | .BLC val right parent_ctx =>
    Zipper.mk n.succ.succ (.rightie val node right) parent_ctx |>.zip_up

  -- Was balanced, deleted from right → becomes leftie (height unchanged → stop)
  | .BRC val left parent_ctx =>
    Zipper.mk n.succ.succ (.leftie val left node) parent_ctx |>.zip_up

  -- Was leftie, deleted from left → becomes balanced (height shrinks → propagate)
  | .LLC val right parent_ctx =>
    rebalance (.balanced val node right) parent_ctx

  -- Was rightie, deleted from right → becomes balanced (height shrinks → propagate)
  | .RRC val left parent_ctx =>
    rebalance (.balanced val left node) parent_ctx

  | .LRC val left parent_ctx => match left with
    -- Left-left: single right rotation (height shrinks → recurse)
    | .leftie nval ll lr =>
      rebalance (.balanced nval ll (.balanced val lr node)) parent_ctx

    -- Balanced sibling: right rotation (height unchanged → stop)
    | .balanced nval ll lr =>
      Zipper.mk n.succ.succ.succ (.rightie nval ll (.leftie val lr node)) parent_ctx |>.zip_up

    -- Left-right: double rotation (height shrinks → recurse)
    | .rightie nval ll lr =>
      rebalance (match n, lr with
        | _, .leftie x t1 t2 => .balanced x (.balanced nval ll t1) (.rightie val t2 node)
        | _, .rightie x t1 t2 => .balanced x (.leftie nval ll t1) (.balanced val t2 node)
        | _, .balanced x t1 t2 => .balanced x (.balanced nval ll t1) (.balanced val t2 node)
        : AVLNode α n.succ.succ) parent_ctx

  | .RLC val right parent_ctx => match right with
    -- Right-right: single left rotation (height shrinks → recurse)
    | .rightie nval rl rr =>
      rebalance (.balanced nval (.balanced val node rl) rr) parent_ctx

    -- Balanced sibling: left rotation (height unchanged → stop)
    | .balanced nval rl rr =>
      Zipper.mk n.succ.succ.succ (.leftie nval (.rightie val node rl) rr) parent_ctx |>.zip_up

    -- Right-left: double rotation (height shrinks → recurse)
    | .leftie nval rl rr =>
      rebalance (match n, rl with
        | _, .rightie x t1 t2 => .balanced x (.leftie val node t1) (.balanced nval t2 rr)
        | _, .leftie x t1 t2 => .balanced x (.balanced val node t1) (.rightie nval t2 rr)
        | _, .balanced x t1 t2 => .balanced x (.balanced val node t1) (.balanced nval t2 rr)
        : AVLNode α n.succ.succ) parent_ctx
termination_by ctx.depth
decreasing_by
  all_goals
  simp_all[Context.depth]

def deleteBST [BEq α] (z : Zipper α) : AVLTree α :=
  let ⟨zn, tree, ctx⟩ := z
  match tree with
  | .balanced _ .nil .nil => rebalance .nil ctx
  | .rightie _ .nil r     => rebalance r   ctx
  | .leftie  _ l   .nil   => rebalance l   ctx
  | _ =>
    match z.value?, z.zip_to_successor with
    | some k, some sz =>
      match sz.value? with
      | some k' =>
        let ⟨szn, sz_tree, sz_ctx⟩ := sz
        match szn, sz_tree with
        | _, .balanced _ .nil .nil => rebalance .nil (sz_ctx.replace_val k k')
        | _, .rightie  _ .nil r    => rebalance r    (sz_ctx.replace_val k k')
        | _, _ => panic! "in-order successor cannot have a left child"
      | none => panic! "successor must be non-nil"
    | _, _ => panic! "non-nil node has no value or no successor"

def AVLTree.delete [Ord α] [BEq α] (tree : AVLTree α) (a : α) : AVLTree α :=
  match tree.unzip.zip_to a with
  |  z => match z.n, z.tree with
    | _, .nil => tree   -- not found, return unchanged
    | _, _    => deleteBST z

-- Things that EXTEND the original blog post:
-- Everything below are random convenience functions, helpers, and some ideas towards correctness proofs..






-- probably not super efficient since the zipper "remembers" (and thus requires space for) the nodes it traversed.
def AVLNode.contains [Ord α] (a: α) (node: AVLNode α n) : Bool :=
  match Zipper.mk n node Context.root
    |>.zip_to a
    |>.value? with
  | some _ => true
  | _ => false

def AVLNode.fold (f : β → α → β → β) (node: AVLNode α n) (acc : β) : β :=
  match node with
    | .nil => acc
    | .balanced x l r => f (l.fold f acc) x (r.fold f acc)
    | .leftie x l r => f (l.fold f acc) x (r.fold f acc)
    | .rightie x l r => f (l.fold f acc) x (r.fold f acc)

def AVLNode.to_list  (node: AVLNode α n) : List α :=
  node.fold (fun x y z => x ++ [y] ++ z) []

def AVLTree.to_list (tree: AVLTree α) : List α := tree.node.to_list

#eval AVLTree.mk 0 .nil |>.insert 3 |>.insert 5 |>.insert 4 |>.insert 1 |>.to_list

def t := AVLTree.mk 0 .nil |>.insert 4 |>.insert 2 |>.insert 6 |>.insert 1 |>.insert 3 |>.insert 5 |>.insert 7
-- Sanity check: sorted order
#eval t.to_list                          -- [1, 2, 3, 4, 5, 6, 7]
-- Delete not found → unchanged
#eval (t.delete 99).to_list             -- [1, 2, 3, 4, 5, 6, 7]
-- Delete a leaf
#eval (t.delete 1).to_list              -- [2, 3, 4, 5, 6, 7]
-- Delete a node with one child
#eval (t.delete 6).to_list              -- [1, 2, 3, 4, 5, 7]
-- Delete the root (two children → replaced by in-order successor 5)
#eval (t.delete 4).to_list              -- [1, 2, 3, 5, 6, 7]
-- Chain of deletes
#eval (t.delete 4 |>.delete 2 |>.delete 6).to_list   -- [1, 3, 5, 7]
-- Delete down to empty
#eval (t.delete 1 |>.delete 2 |>.delete 3 |>.delete 4 |>.delete 5 |>.delete 6 |>.delete 7).to_list  -- []


-- TODO: With this we could prove the ordering and set properties of an AVL Tree.

def AVLNode.map (f : α → β) (node: AVLNode α n) : AVLNode β n :=
  match node with
    | .nil => .nil
    | .balanced x l r => .balanced (f x) (l.map f) (r.map f)
    | .leftie x l r => .leftie (f x) (l.map f) (r.map f)
    | .rightie x l r => .rightie (f x) (l.map f) (r.map f)

def AVLTree.map (f : α → β) (tree: AVLTree α) : AVLTree β := {tree with node := tree.node.map f}



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
  rw [Nat.add_assoc, Nat.add_comm]
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


def Context.node_count : (c: Context α n) → Nat
  | .root => 0
  | .BLC _ a b => a.node_count + b.node_count
  | .BRC _ a b => a.node_count + b.node_count
  | .LLC _ a b => a.node_count + b.node_count
  | .LRC _ a b => a.node_count + b.node_count
  | .RLC _ a b => a.node_count + b.node_count
  | .RRC _ a b => a.node_count + b.node_count

theorem zero_lt_node_count (t : AVLNode α n) : 0 < t.node_count := by
  induction t
  . simp[AVLNode.node_count]
  all_goals
  simp[AVLNode.node_count, Nat.add_pos_iff_pos_or_pos]

theorem left_child_smaller (t : AVLNode α n) {m : Nat} {child : AVLNode α m}
  (h : some ⟨m, child⟩ = t.left_child) : child.node_count < t.node_count := by
  dsimp[AVLNode.left_child] at h
  cases t
  . simp_all
  all_goals
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
