use std::error::Error;
use plotters::chart::DualCoordChartContext;
use plotters::coord::ranged1d::ValueFormatter;
use plotters::prelude::*;
use crate::graphing::graph_renderer::GraphRenderer;


impl GraphRenderer {
	pub(super) fn set_x_axis_as_rounds<'a, DB, X, Y, XT, YT>(
		&self,
		chart: &mut ChartContext<'a, DB, Cartesian2d<X, Y>>,
	) -> Result<(), Box<dyn Error>>
	where
		DB: DrawingBackend + 'a,
		DB::ErrorType: 'static,
		X: Ranged<ValueType = XT> + ValueFormatter<XT>,
		Y: Ranged<ValueType = YT> + ValueFormatter<YT>,
	{
		chart
			.configure_mesh()
			.disable_mesh()
			.disable_y_axis()
			.x_desc("Compression Rounds")
			.label_style(self.text_style.with_color(&BLACK))
			.draw()?;
		Ok(())
	}

	pub(super) fn set_y_axis<'a, DB, X, Y, XT, YT>(
		&self,
		chart: &mut ChartContext<'a, DB, Cartesian2d<X, Y>>,
		label: &str,
		color: Option<RGBAColor>,
		formatter: Option<&dyn Fn(&YT) -> String>,
	) -> Result<(), Box<dyn Error>>
	where
		DB: DrawingBackend + 'a,
		DB::ErrorType: 'static,
		X: Ranged<ValueType = XT> + ValueFormatter<XT>,
		Y: Ranged<ValueType = YT> + ValueFormatter<YT>,
		YT: 'a,
	{
		let color = color.unwrap_or(BLACK.to_rgba());
		let mut builder = chart.configure_mesh();

		if let Some(formatter) = formatter {
			builder.y_label_formatter(formatter);
		}

		builder
			.disable_mesh()
			.disable_x_axis()
			.y_desc(label)
			.label_style(self.text_style.with_color(color))
			.draw()?;
		Ok(())
	}

	pub(super) fn set_secondary_y_axis<'a, DB, X, Y1, Y2, XT, YT1, YT2>(
		&self,
		chart: &mut DualCoordChartContext<'a, DB, Cartesian2d<X, Y1>, Cartesian2d<X, Y2>>,
		label: &str,
		color: Option<RGBAColor>,
		formatter: Option<&dyn Fn(&YT2) -> String>,
	) -> Result<(), Box<dyn Error>>
	where
		DB: DrawingBackend + 'a,
		DB::ErrorType: 'static,
		X: Ranged<ValueType = XT> + ValueFormatter<XT>,
		Y1: Ranged<ValueType = YT1> + ValueFormatter<YT1>,
		Y2: Ranged<ValueType = YT2> + ValueFormatter<YT2>,
	{
		let color = color.unwrap_or(BLACK.to_rgba());
		let mut builder = chart.configure_secondary_axes();

		if let Some(formatter) = formatter {
			builder.y_label_formatter(formatter);
		}

		builder
			.y_desc(label)
			.label_style(self.text_style.with_color(color))
			.draw()?;
		Ok(())
	}

	// TODO: Implement discontinue_line for draw_series and draw_secondary_series

	pub(super) fn draw_series<'a, DB, X, Y, XT, YT>(
		&self,
		chart: &mut ChartContext<'a, DB, Cartesian2d<X, Y>>,
		data: Vec<(XT, YT)>,
		with_points: bool,
		discontinue_line: bool,
		label: &str,
		color: Option<RGBAColor>,
	) -> Result<(), Box<dyn Error>>
	where
		DB: DrawingBackend + 'a,
		DB::ErrorType: 'static,
		X: Ranged<ValueType = XT> + ValueFormatter<XT>,
		Y: Ranged<ValueType = YT> + ValueFormatter<YT>,
		XT: Clone + 'static,
		YT: Clone + 'static,
	{
		let color = color.unwrap_or(BLACK.to_rgba());

		chart
			.draw_series(LineSeries::new(
				data.clone(),
				ShapeStyle {
					color: color.to_rgba(),
					filled: false,
					stroke_width: self.line_thickness,
				}
			))?
			.label(label)
			.legend(move |(x, y)| PathElement::new(vec![(x, y), (x + 20, y)], color));

		if with_points {
			chart.draw_series(PointSeries::of_element(
				data,
				3,
				color,
				&|c, s, st| Circle::new(c, s, st.filled()),
			))?;
		}

		Ok(())
	}

	pub(super) fn draw_secondary_series<'a, DB, X, Y1, Y2, XT, YT1, YT2>(
		&self,
		chart: &mut DualCoordChartContext<'a, DB, Cartesian2d<X, Y1>, Cartesian2d<X, Y2>>,
		data: Vec<(XT, YT2)>,
		with_points: bool,
		discontinue_line: bool,
		label: &str,
		color: Option<RGBAColor>,
	) -> Result<(), Box<dyn Error>>
	where
		DB: DrawingBackend + 'a,
		DB::ErrorType: 'static,
		X: Ranged<ValueType = XT> + ValueFormatter<XT>,
		Y1: Ranged<ValueType = YT1> + ValueFormatter<YT1>,
		Y2: Ranged<ValueType = YT2> + ValueFormatter<YT2>,
		XT: Clone + 'static,
		YT1: Clone + 'static,
		YT2: Clone + 'static,
	{
		let color = color.unwrap_or(BLACK.to_rgba());

		chart
			.draw_secondary_series(LineSeries::new(
				data.clone(),
				ShapeStyle {
					color: color.to_rgba(),
					filled: false,
					stroke_width: self.line_thickness,
				}
			))?
			.label(label)
			.legend(move |(x, y)| PathElement::new(vec![(x, y), (x + 20, y)], color));

		if with_points {
			chart.draw_secondary_series(PointSeries::of_element(
				data,
				3,
				color,
				&|c, s, st| Circle::new(c, s, st.filled()),
			))?;
		}

		Ok(())
	}

	pub(super) fn draw_legend<'a, DB, CT>(
		&self,
		chart: &mut ChartContext<'a, DB, CT>,
	) -> Result<(), Box<dyn Error>>
	where
		DB: DrawingBackend + 'a,
		DB::ErrorType: 'static,
		CT: CoordTranslate + 'a,
	{
		chart
			.configure_series_labels()
			.background_style(RGBAColor(140, 140, 140, 0.3))
			.position(SeriesLabelPosition::LowerRight)
			.draw()?;
		Ok(())
	}
}
