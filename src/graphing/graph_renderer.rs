use std::error::Error;
use std::fs;
use std::path::PathBuf;
use plotters::prelude::RGBAColor;
use crate::data::data_retriever::DataRetriever;
use crate::graphing::line_styles::LineStyle;
use crate::structs::collision_type::CollisionType;
use crate::structs::hash_function::HashFunction;


pub struct GraphRenderer {
	pub(super) output_dir: PathBuf,
	pub(super) output_size: (u32, u32),
	pub(super) title_style: (&'static str, u32),
	pub(super) text_style: (&'static str, u32),
	pub(super) line_styles: Box<[LineStyle]>,
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
		line_styles: Box<[LineStyle]>,
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
			line_styles,
			line_thickness,
			point_thickness,
			data_retriever,
		})
	}

	#[allow(dead_code)]
	pub fn default() -> Result<Self, Box<dyn Error>> {
		use LineStyle::*;

		Ok(GraphRenderer {
			output_dir: PathBuf::from("graphs/"),
			output_size: (1024, 768),
			title_style: ("noto sans", 36),
			text_style: ("noto sans", 14),
			line_styles: Box::from([
				// Maroon
				Normal {
					color: RGBAColor(166, 30, 77, 1.0),
				},
				// Dark Blue
				Normal {
					color: RGBAColor(24, 100, 171, 1.0),
				},
				// Green
				Normal {
					color: RGBAColor(8, 127, 91, 1.0),
				},
				// Yellow
				Normal {
					color: RGBAColor(250, 176, 5, 1.0),
				},
				// Purple
				Normal {
					color: RGBAColor(156, 54, 181, 1.0),
				},
				// Cyan
				Dashed {
					color: RGBAColor(12, 133, 153, 1.0),
					size: 10,
					spacing: 20,
				},
				// Light Purple
				Dashed {
					color: RGBAColor(95, 61, 196, 1.0),
					size: 10,
					spacing: 20,
				},
				// Light Green
				Dashed {
					color: RGBAColor(70, 210, 94, 1.0),
					size: 10,
					spacing: 20,
				},
				// Light Blue
				Dashed {
					color: RGBAColor(116, 143, 252, 1.0),
					size: 10,
					spacing: 20,
				},
				// Black
				Normal {
					color: RGBAColor(0, 0, 0, 1.0),
				},
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
