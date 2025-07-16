import Canonical.Main

axiom add_comm' [Add X] (n m : X) : n + m = m + n

theorem add_comm [Add X] (n m : X) : n + m = m + n := by
  canonical +debug [add_comm']
