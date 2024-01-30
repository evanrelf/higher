module Higher
  ( higher
  )
where

import Language.Haskell.TH (Dec, Name, Q)

higher :: Name -> Q [Dec]
higher _name = pure []
