use plotters::prelude::RGBAColor;

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
		match self {
			LineStyle::Normal { color, .. } => color,
			LineStyle::Dashed { color, .. } => color,
		}
	}
}
