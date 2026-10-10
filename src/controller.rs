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

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;
    use rstest::rstest;

    #[rstest]
    #[case::inside(0.15, 0.0)]
    #[case::inside_negative(-0.15, 0.0)]
    #[case::edge_counts_as_input(GAMEPAD_DEADZONE, GAMEPAD_DEADZONE)]
    #[case::outside(-0.7, -0.7)]
    fn axis_zeroes_values_inside_the_deadzone(#[case] input: f32, #[case] expected: f32) {
        assert_eq!(axis(input), expected);
    }

    #[rstest]
    #[case::inside(Vec2::new(0.1, -0.1), Vec2::ZERO)]
    // Each component is inside the deadzone but the length (≈0.17) is not.
    #[case::radial_not_per_axis(Vec2::new(0.12, -0.12), Vec2::new(0.12, -0.12))]
    #[case::edge_counts_as_input(
        Vec2::new(0.0, GAMEPAD_DEADZONE),
        Vec2::new(0.0, GAMEPAD_DEADZONE)
    )]
    #[case::outside(Vec2::new(0.0, -0.9), Vec2::new(0.0, -0.9))]
    fn stick_deadzone_is_radial(#[case] input: Vec2, #[case] expected: Vec2) {
        assert_eq!(stick(input), expected);
    }

    proptest! {
        #[test]
        fn axis_passes_through_or_zeroes(value in -1.0_f32..=1.0) {
            let expected = if value.abs() < GAMEPAD_DEADZONE { 0.0 } else { value };
            prop_assert_eq!(axis(value), expected);
        }

        #[test]
        fn stick_passes_through_or_zeroes(x in -1.0_f32..=1.0, y in -1.0_f32..=1.0) {
            let input = Vec2::new(x, y);
            let expected = if input.length() < GAMEPAD_DEADZONE { Vec2::ZERO } else { input };
            prop_assert_eq!(stick(input), expected);
        }
    }
}
