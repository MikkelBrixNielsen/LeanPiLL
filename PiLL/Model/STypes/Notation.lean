import PiLL.Model.STypes.Basic

infixr:90 " ⨂ " => Types.tensor
infixr:90 " ⊕ " => Types.oplus
infixr:90 " ⅋ " => Types.parr
infixr:90 " & " => Types.amp

instance : One Types := ⟨Types.one⟩
instance : Bot Types := ⟨Types.bot⟩

prefix:95 "??" => Types.quest
prefix:95 "!!" => Types.bang

prefix:max "∃․" => Types.exists_
prefix:max "∀․" => Types.forall_

postfix:max "ᗮ" => Types.dual

infix:90 " ⊸ " => Types.linImpl
