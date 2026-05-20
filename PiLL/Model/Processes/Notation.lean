import PiLL.Model.Processes.Basic

notation:80 x "⟦⟧․" P => Proc.one x P
notation:80 x "⟦•⟧․" P => Proc.tensor x P
notation:80 x "⟦" A "⟧․" P => Proc.output x P A
notation:80 x "⸨⸩․" P => Proc.bot x P
notation:80 x "⸨•⸩․" P => Proc.parr x P
notation:80 x "⸨⋄⸩․" P => Proc.input x P

notation:75 "𝑣⸨•,•⸩ " P:80 => Proc.cut P
notation:80 x "⟦𝐋⟧․" P:80 => Proc.selectL x P
notation:80 x "⟦𝐑⟧․" P:80 => Proc.selectR x P
notation:80 x "⟦USE⟧․" P:80 => Proc.consume x P
notation:80 x "⟦DUP⟧⸨•⸩․" P:80 => Proc.duplicate x P
notation:80 x "⟦DISP⟧․" P:80 => Proc.dispose x P
notation:80 "!" x "․{" P:80 "}" => Proc.server x ∅ P
notation:80 "!" x "⟨" zs "⟩․{" P:80 "}" => Proc.server x zs P
notation:80 x "․case{𝐋" " : " P:80 ", " "𝐑" " : " Q :80"}" => Proc.amp x P Q

notation:80 x "⟷ₚ" y => Proc.link x y
infixr:70 " |ₚ " => Proc.par
notation "𝟘" => Proc.nil
