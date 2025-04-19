use std::error::Error;
use std::fs;
use std::ops::Range;
use std::path::PathBuf;
use plotters::prelude::RGBColor;
use crate::data::data_retriever::DataRetriever;
use crate::structs::collision_type::CollisionType;
use crate::structs::hash_function::HashFunction;


pub struct GraphRenderer {
	pub(super) output_dir: PathBuf,
	pub(super) output_size: (u32, u32),
	pub(super) title_style: (&'static str, u32),
	pub(super) text_style: (&'static str, u32),
	pub(super) color_palette: Box<[RGBColor]>,
	pub(super) line_thickness: u32,
	pub(super) data_retriever: DataRetriever,
}

impl GraphRenderer {
	pub fn new(
		output_dir: PathBuf,
		output_size: (u32, u32),
		title_style: (&'static str, u32),
		text_style: (&'static str, u32),
		color_palette: Box<[RGBColor]>,
		line_thickness: u32,
		data_retriever: DataRetriever,
	) -> Result<Self, Box<dyn Error>> {
		if !output_dir.exists() {
			fs::create_dir_all(output_dir.clone())?;
		}

		Ok(GraphRenderer {
			output_dir,
			output_size,
			title_style,
			text_style,
			color_palette,
			line_thickness,
			data_retriever,
		})
	}

	#[allow(dead_code)]
	pub fn default() -> Self {
		GraphRenderer {
			output_dir: PathBuf::from("graphs/"),
			output_size: (1024, 768),
			title_style: ("noto sans", 36),
			text_style: ("noto sans", 14),
			color_palette: Box::from([
				RGBColor(166, 30, 77), // Maroon
				RGBColor(24, 100, 171), // Dark Blue
				RGBColor(8, 127, 91), // Green
				RGBColor(250, 176, 5), // Yellow
				RGBColor(156, 54, 181), // Purple
				RGBColor(12, 133, 153), // Cyan
				RGBColor(95, 61, 196), // Light Purple
				RGBColor(70, 210, 94), // Light Green
				RGBColor(116, 143, 252), // Light Blue
			]),
			line_thickness: 2,
			data_retriever: DataRetriever::default(),
		}
	}

	pub(super) fn calculate_percent_dev(
		&self,
		baseline_range: Range<u128>,
		deviation_range: Range<u128>,
		buffer_percent: f64
	) -> Range<f64> {
		let lower_percentage = (deviation_range.start as f64 - baseline_range.start as f64) /
			baseline_range.start as f64 * 100.0;

		let upper_percentage = (deviation_range.end as f64 - baseline_range.end as f64) /
			baseline_range.end as f64 * 100.0;

		let min_val = lower_percentage.min(upper_percentage);
		let max_val = lower_percentage.max(upper_percentage);

		let range_size = max_val - min_val;
		let buffer = range_size * buffer_percent / 100.0;

		(min_val - buffer)..(max_val + buffer)
	}
}

#[derive(thiserror::Error, Debug, PartialEq, Clone)]
pub enum GraphRendererError<'a> {
	#[error("failed to get range for {variable}")]
	GetRangeFailed {
		variable: &'a str,
	},
	#[error("failed to generate chart {hash_function} {collision_type}: {err}")]
	FailedToGenerate {
		hash_function: HashFunction,
		collision_type: CollisionType,
		err: &'a str,
	},
	#[error("{graph_name} graph generation - {dataset_name} data cannot be empty!")]
	MissingData {
		graph_name: &'a str,
		dataset_name: &'a str,
	},
}
