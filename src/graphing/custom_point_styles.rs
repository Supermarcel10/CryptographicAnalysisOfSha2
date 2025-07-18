use plotters::prelude::*;
use std::error::Error;
use num_traits::One;
use std::ops::Add;
use plotters::coord::ranged1d::ValueFormatter;

#[derive(PartialEq)]
#[allow(dead_code)]
pub enum PointStyles {
	None,
	Basic,
	Custom,
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
		X: Ranged<ValueType=XT> + ValueFormatter<XT>,
		Y: Ranged<ValueType=YT> + ValueFormatter<YT>,
		XT: Clone + Copy + Add<Output=XT> + PartialOrd + 'static + One,
		YT: Clone + 'static,
	{
		match self {
			PointStyles::None => Ok(()), // Do nothing
			PointStyles::Basic => self.draw_basic(chart, data, color, point_thickness),
			PointStyles::Custom => self.draw_custom(chart, data, color, point_thickness),
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
		X: Ranged<ValueType=XT> + ValueFormatter<XT>,
		Y: Ranged<ValueType=YT> + ValueFormatter<YT>,
		XT: Clone + Copy + Add<Output=XT> + PartialOrd + 'static + One,
		YT: Clone + 'static,
	{
		let color = color.unwrap_or(BLACK.to_rgba());

		chart.draw_series(PointSeries::of_element(
			data,
			point_thickness,
			color,
			&|coord, size, style| Circle::new(coord, size, style.filled())
		))?;

		Ok(())
	}

	fn draw_custom<'a, DB, X, Y, XT, YT>(
		&self,
		chart: &mut ChartContext<'a, DB, Cartesian2d<X, Y>>,
		data: Vec<(XT, YT)>,
		color: Option<RGBAColor>,
		point_thickness: u32,
	) -> Result<(), Box<dyn Error>>
	where
		DB: DrawingBackend + 'a,
		DB::ErrorType: 'static,
		X: Ranged<ValueType=XT> + ValueFormatter<XT>,
		Y: Ranged<ValueType=YT> + ValueFormatter<YT>,
		XT: Clone + Copy + Add<Output=XT> + PartialOrd + 'static + One,
		YT: Clone + 'static,
	{
		let color = color.unwrap_or(BLACK.to_rgba());

		chart.draw_series(PointSeries::of_element(
			data,
			point_thickness,
			color,
			&|coord, size, style| Circle::new(coord, size, style.filled())
		))?;

		Ok(())
	}
}
