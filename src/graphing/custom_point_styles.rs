use num_traits::One;
use plotters::coord::ranged1d::ValueFormatter;
use plotters::prelude::*;
use std::error::Error;
use std::ops::Add;

#[derive(Debug, Clone, Copy, PartialEq)]
#[allow(dead_code)]
pub enum CustomShape {
	None,
	Circle,
	Cross,
	Triangle,
}

#[allow(dead_code)]
pub enum PointStyles {
	None,
	Basic,
	Custom { shapes: Vec<CustomShape> },
}

impl PointStyles {
	pub fn draw<'a, DB, X, Y, XT, YT>(
		&self,
		chart: &mut ChartContext<'a, DB, Cartesian2d<X, Y>>,
		data: Vec<(XT, YT)>,
		color: Option<RGBAColor>,
		point_thickness: u32,
	) -> Result<(), Box<dyn Error>>
	where
		DB: DrawingBackend + 'a,
		DB::ErrorType: 'static,
		X: Ranged<ValueType = XT> + ValueFormatter<XT>,
		Y: Ranged<ValueType = YT> + ValueFormatter<YT>,
		XT: Clone + Copy + Add<Output = XT> + PartialOrd + 'static + One,
		YT: Clone + Add<Output = YT> + One + 'static,
	{
		match self {
			PointStyles::None => Ok(()), // Do nothing
			PointStyles::Basic => self.draw_basic(chart, data, color, point_thickness),
			PointStyles::Custom { shapes } => {
				self.draw_with_custom_shapes(chart, data, color, point_thickness, shapes.clone())
			}
		}
	}

	fn draw_basic<'a, DB, X, Y, XT, YT>(
		&self,
		chart: &mut ChartContext<'a, DB, Cartesian2d<X, Y>>,
		data: Vec<(XT, YT)>,
		color: Option<RGBAColor>,
		point_thickness: u32,
	) -> Result<(), Box<dyn Error>>
	where
		DB: DrawingBackend + 'a,
		DB::ErrorType: 'static,
		X: Ranged<ValueType = XT> + ValueFormatter<XT>,
		Y: Ranged<ValueType = YT> + ValueFormatter<YT>,
		XT: Clone + Copy + Add<Output = XT> + PartialOrd + 'static + One,
		YT: Clone + 'static,
	{
		let color = color.unwrap_or(BLACK.to_rgba());

		chart.draw_series(PointSeries::of_element(
			data,
			point_thickness,
			color,
			&|coord, size, style| Circle::new(coord, size, style.filled()),
		))?;

		Ok(())
	}

	fn draw_with_custom_shapes<'a, DB, X, Y, XT, YT>(
		&self,
		chart: &mut ChartContext<'a, DB, Cartesian2d<X, Y>>,
		data: Vec<(XT, YT)>,
		color: Option<RGBAColor>,
		point_thickness: u32,
		shapes: Vec<CustomShape>,
	) -> Result<(), Box<dyn Error>>
	where
		DB: DrawingBackend + 'a,
		DB::ErrorType: 'static,
		X: Ranged<ValueType = XT> + ValueFormatter<XT>,
		Y: Ranged<ValueType = YT> + ValueFormatter<YT>,
		XT: Clone + Copy + Add<Output = XT> + PartialOrd + 'static + One,
		YT: Clone + Add<Output = YT> + One + 'static,
	{
		let color = color.unwrap_or(BLACK.to_rgba());

		// Group data points by their shape type
		let mut circles = Vec::new();
		let mut crosses = Vec::new();
		let mut triangles = Vec::new();

		let data_with_shapes: Vec<((XT, YT), CustomShape)> = data
			.into_iter()
			.zip(shapes)
			.collect();

		for ((x, y), shape) in &data_with_shapes {
			match shape {
				CustomShape::Circle => circles.push((*x, y.clone())),
				CustomShape::Cross => crosses.push((*x, y.clone())),
				CustomShape::Triangle => triangles.push((*x, y.clone())),
				CustomShape::None => (),
			}
		}

		// Draw each shape type as a separate series
		if !circles.is_empty() {
			chart.draw_series(PointSeries::of_element(
				circles,
				point_thickness,
				color,
				&|coord, size, style| Circle::new(coord, size, style.filled()),
			))?;
		}

		if !crosses.is_empty() {
			chart.draw_series(PointSeries::of_element(
				crosses,
				point_thickness,
				color,
				&|coord, size, style| Cross::new(coord, size * 2, style.filled()),
			))?;
		}

		if !triangles.is_empty() {
			chart.draw_series(PointSeries::of_element(
				triangles,
				point_thickness,
				color,
				&|coord, size, style| {
					TriangleMarker::new(coord, (size as f32) * 1.8, style.filled())
				},
			))?;
		}

		Ok(())
	}
}
