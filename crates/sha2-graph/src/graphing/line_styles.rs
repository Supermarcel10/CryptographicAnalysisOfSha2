use plotters::prelude::{Color, RGBAColor};
use plotters::style::ShapeStyle;

#[derive(Copy, Clone)]
pub enum LineStyle {
	Normal {
		color: RGBAColor,
	},
	Dashed {
		color: RGBAColor,
		size: u32,
		spacing: u32,
	},
}

impl LineStyle {
	pub(super) fn get_color(&self) -> &RGBAColor {
		use LineStyle::*;

		match self {
			Normal { color, .. } => color,
			Dashed { color, .. } => color,
		}
	}

	pub(super) fn get_legend_style(&self) -> ShapeStyle {
		use LineStyle::*;

		match self {
			Normal { color, .. } => color.filled(),
			Dashed { color, .. } => color.into(),
		}
	}
}
