use bevy::prelude::*;

pub const GAMEPAD_DEADZONE: f32 = 0.16;

pub fn active_gamepad<'w, 's>(gamepads: &'w Query<'w, 's, &Gamepad>) -> Option<&'w Gamepad> {
    gamepads.iter().next()
}

pub fn axis(value: f32) -> f32 {
    if value.abs() < GAMEPAD_DEADZONE {
        0.0
    } else {
        value
    }
}

pub fn stick(value: Vec2) -> Vec2 {
    if value.length() < GAMEPAD_DEADZONE {
        Vec2::ZERO
    } else {
        value
    }
}
