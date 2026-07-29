A while ago, I read https://fedelebron.com/compile-time-invariants-in-haskell. In that blogpost, the author is using Haskell to build an AVL Tree, that is guaranteed to be balanced.
In theory every AVL Tree should be guaranteed to be balanced - that's the AVL tree invariant after all. What the blog post demonstrates is how to use the type checker (with DataKinds extension) to guarantee that the programmer can not make a mistake and accidentally produce unbalanced AVL trees.

I wanted to take the chance and explore if we can do the same in Lean4, a dependently typed language. The type system of Lean4 should be stronger than Haskells and as a bonus we can also use Lean4 as a theorem prover and thus prove certain properties of our AVL trees.

That being said, I am a total beginner in Lean4, so the biggest drawback here is that all functions should be total. That means in this implementation they need to return Option types, and also the termination prover has to agree that all the (recursive) functions indeed terminate.

Other than that most changes from the original blog post are syntactical or replacing features that are differ from Haskell. For example the `ExistentialQuantification` on the `Zipper` seemed impossible in Lean. Instead, the Zipper does expose the height `n` of the tree that it is zipping through as a value. Same for the `AVLTree` that needs to hold the `n` (but moves it from a type-level to a value-level parameter).

That all being said, I would heavily recommend you to first read https://fedelebron.com/compile-time-invariants-in-haskell and then return as I will not explain every concept in depth here and mostly focus on what I did differently to make it work in Lean or where I diverged from the original implementation and why.


### AVL Data Type

Like in Haskell, we are using a GADT to show the 4 cases for nodes in an AVL Tree:
- Leaf (height 0; no child, no value)
- Balanced (height n+1; Constructed from 2 children of height n)
- Leftie (height n+1; Constructed from a left child of height n+1 and a right child of height n)
- Rightie (height n+1; Constructed from a left child of height n and a right child of height n+1)

All the non-leaf cases also carry a value.

```
inductive AVLNode (α : Type) : Nat → Type where
  | nil : AVLNode α 0
  | balanced : α → AVLNode α n → AVLNode α n → AVLNode α (n + 1)
  | leftie : α → AVLNode α (n + 1) → AVLNode α n → AVLNode α (n + 2)
  | rightie : α → AVLNode α n → AVLNode α (n + 1) → AVLNode α (n + 2)
deriving Repr, BEq
```

And a few examples:
```
set_option eval.type true

#eval AVLNode.balanced 3 AVLNode.nil AVLNode.nil
#eval AVLNode.leftie 3 (AVLNode.balanced 2 AVLNode.nil AVLNode.nil) AVLNode.nil
#eval @AVLNode.leftie Nat 0 3 (AVLNode.balanced 2 AVLNode.nil AVLNode.nil) AVLNode.nil

#eval AVLNode.rightie 3 AVLNode.nil (AVLNode.balanced 2 AVLNode.nil AVLNode.nil)
#eval @AVLNode.rightie Nat 0 3 AVLNode.nil (AVLNode.balanced 2 AVLNode.nil AVLNode.nil)
```

In the last example, we used `@AVLNode` to also pass the inferred type parameters (TODO CHECK) directly. Namely, that this is an `AVLTree` holding `Nat` and that the depth of the current node is 0 (TODO CHECK).

### Navigating through the tree

Thanks to reading this in the original blogpost, I first learned about the concept of `Zipper` which is honestly super cool. Definitely check (TODO INSERT LINK) out if you haven't heard about it before.

The context for our Zipper is:
```
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
```

And the actual Zipper:
```
structure Zipper (α : Type) : Type where
  n : Nat
  tree : AVLNode α n
  ctx : Context α n
deriving Repr, BEq
```
This is the first obvious deviation from haskells `forall` that nicely hides `n` inside the Zipper. In `Lean` the best I could do was get the `n` from type level (as in the first argument of `AvlNode` or `Context` type constructors) into value level as a member of the `Zipper` structure. I believe that this is only possible because we have dependent types: The *type* of `tree` (and `ctx`) depends on the *value* of `n`.

A few examples here as well:
```
#eval (@Zipper.mk Nat 0 (AVLNode.nil) (Context.root))
#eval Zipper.mk 1 (AVLNode.balanced 3 AVLNode.nil AVLNode.nil) (Context.root)
#eval Zipper.mk 0 (AVLNode.nil) (Context.BLC 3 (AVLNode.nil) Context.root)
```

Implementing navigation for the zipper is straightforward, although very verbose. Note that we have to deconstruct the zipper before matching with `let {tree, ctx, ..} := z`. That is because (TODO CHECK).

```
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
```


Now for some actual Lean things. We have a Zipper that can go down, to the left or the right and up again.
That sounds like we could prove that if we first go down and then up, we are back at our starting point.

And indeed, we can. The theorem `go_left_up` states that for any zipper `z`, if there exists a zipper `new_z` that we get by going left from `z`, then going up from `new_z` gets us back to `z`. The proof is by applying the definitions of `go_left` and `go_up` and making a case distinction over all possible cases of `AVLNode` (balanced, left-heavy or right-heavy) that the zipper could be at.

```
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
```

Good riddance that we just started with proofs because we need some for the next step as well. `Zipper.zip_to` is a recursive function and Lean requires all functions to be total. That means no infinite recursion. To prove that our function is indeed not looping endlessly, we make an argument that there is something that decreases in every function call.
For `Zipper`, that will be `n`; the depth of the remaining subtree. So we have to start with some small theorems about what happens to `n` when we `go_left` or `go_right`.

These theorems state that if we have a zipper, and we get a new zipper by calling `go_left` on it, then the new zipper will have a smaller `n` than the one we started with ... which is quite logical since `n` is the height of the tree and we are walking downwards. The proofs seem to agree with our logic and are also straight forward.

```
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
```

Equipped with these 2 theorems, we can now implement `zip_to` - and not only implement it but also show that it terminates:
```
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
```

Note the `termination_by z.n` line that says "we prove termination by `z.n` decreasing in every step". Then there's 2 `have` statements in the code that are not getting executed, but putting the fact that `lz.n` and `rz.n` vice-versa are smaller than `z.n` into the provers context.

### AVL Tree

So far, we only defined `AVLNode` which is not a great API since external users shouldn't have to deal with internal balancing cases. It  alsomakes sense to 'hide' the dependent type parameter `n`..., that's what the Haskell blogpost does at least. I didn't find a good way to do so, so again I just stuffed it into the value space. While we're at it, we can also create a default empty instance for an AVLTree and a few conveniences to create a tree from a node or a zipper from a tree.

```
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
```

The reverse is also useful: going from a `Zipper` back to an `AVLTree`. We call this `Zipper.zip_up`. It is again a recursive function so let's first do some legwork and prove a few properties that we need in a bit.

We define the depth of a context as the length of the 'chain' of contexts that we are down in the tree. Then the theorem that follows is that while we go up, the depth decreases.

```
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
```

And lastly we can define our `zip_up` method and prove that it will terminate. We try to go up as long as we can - and once that doesn't work we are sure that we are at the root.
```
def Zipper.zip_up (z : Zipper α) : AVLTree α :=
    match c: z.go_up with
    | some upper =>
      have : upper.ctx.depth < z.ctx.depth := by simp_all[zipper_go_up_ctx_depth_lt]
      upper.zip_up
    | none => AVLTree.mk z.n z.tree
termination_by z.ctx.depth
```
