import PiLL.Model.STypes.Shift

-- Eager shifting
-- k act as target index s.t. A is inserted at depth k, binderes shfit k by 1 to ensure
-- when depth k is reached A can be inserted safely
    -- if i == k, target depth reached insert A
    -- if i > k, outside binder => decrement to compress an account for i == k being explicit now
    -- if i < k, inside binder do nothing => keep i
-- in B replace all index k with explicit A
def Types.subst (B A : Types) (k : Nat) : Types :=
  match B with
  | .var (.bound i) =>
      if i == k then A
      else if i > k then .var (.bound (i - 1))
      else .var (.bound i)
  | .varDual (.bound i) =>
      if i == k then (.dual A)
      else if i > k then .varDual (.bound (i - 1))
      else .varDual (.bound i)
  | .var (.free i)        => .var (.free i)       -- don't touch free
  | .varDual (.free i)    => .varDual (.free i)   -- don't touch free
  | .forall_ B            => .forall_ (B.subst (shift 0 1 A) (k + 1))
  | .exists_ B            => .exists_ (B.subst (shift 0 1 A) (k + 1))
  | .tensor L R           => .tensor (L.subst A k) (R.subst A k)
  | .parr L R             => .parr (L.subst A k) (R.subst A k)
  | .quest B              => .quest (B.subst A k)
  | .bang B               => .bang (B.subst A k)
  | .amp L R              => .amp (L.subst A k) (R.subst A k)
  | .oplus L R            => .oplus (L.subst A k) (R.subst A k)
  | t                     => t -- one | bot | atom | atomDual (Don't have Types to subst)

instance : HasSubst Types Types Nat where subst := Types.subst
