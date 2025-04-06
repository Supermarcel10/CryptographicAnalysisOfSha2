use std::path::PathBuf;
use plotters::prelude::RGBColor;

pub struct GraphRenderer {
	pub(super) output_directory: PathBuf,
	pub(super) output_size: (u32, u32),
	pub(super) title_style: (&'static str, u32),
	pub(super) text_style: (&'static str, u32),
	pub(super) color_palette: Box<[RGBColor]>,
	pub(super) line_thickness: u32,
}

impl GraphRenderer {
	pub fn new(
		output_directory: PathBuf,
		output_size: (u32, u32),
		title_style: (&'static str, u32),
		text_style: (&'static str, u32),
		color_palette: Box<[RGBColor]>,
		line_thickness: u32,
	) -> Self {
		GraphRenderer {
			output_directory,
			output_size,
			title_style,
			text_style,
			color_palette,
			line_thickness,
		}
	}

	pub fn default() -> Self {
		GraphRenderer {
			output_directory: PathBuf::from("graphs/"),
			output_size: (1024, 768),
			title_style: ("noto sans", 36),
			text_style: ("noto sans", 14),
			color_palette: Box::from([
				RGBColor(37, 95, 133),
				RGBColor(140, 33, 85),
				RGBColor(221, 164, 72),
				RGBColor(50, 150, 93),
				RGBColor(0, 0, 0),
			]),
			line_thickness: 2,
		}
	}
}

#[derive(thiserror::Error, Debug, PartialEq, Clone)]
pub enum GraphRendererError<'a> {
	#[error("failed to get range for {variable}")]
	GetRangeFailed {
		variable: &'a str,
	},
}
