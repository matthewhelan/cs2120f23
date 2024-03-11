inductive State
| s0
| s120
| s24

inductive Rotations
| r0
| r120
| r240

def act : Rotation → Rotation → Rotation := _

def add_rotation : Rotation → Rotation → Rotation
| r0, r => r
| r, r0 => r
| r120, r120 => r120


def sub_state : State → State → Rotation
| s0, s0 => r0
| s0, s120 => r240
|
