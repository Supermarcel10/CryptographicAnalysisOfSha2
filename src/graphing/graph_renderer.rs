use std::error::Error;
use std::fs;
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
	pub(super) point_thickness: u32,
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
		point_thickness: u32,
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
			point_thickness,
			data_retriever,
		})
	}

	#[allow(dead_code)]
	pub fn default() -> Result<Self, Box<dyn Error>> {
		Ok(GraphRenderer {
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
				RGBColor(0, 0, 0), // Black
			]),
			line_thickness: 2,
			point_thickness: 6,
			data_retriever: DataRetriever::default()?,
		})
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
