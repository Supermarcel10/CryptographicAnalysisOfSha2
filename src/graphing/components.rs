use std::error::Error;
use std::ops::Add;
use num_traits::One;
use plotters::chart::DualCoordChartContext;
use plotters::coord::ranged1d::ValueFormatter;
use plotters::prelude::*;
use crate::graphing::graph_renderer::GraphRenderer;
use crate::graphing::utils::split_data;

/// Generalized components for reuse in graphs.
impl GraphRenderer {
	/// Set the X-Axis to Compression Rounds
	///
	/// # Arguments
	///
	/// * `chart`: The chart to add axis to.
	///
	/// # Returns
	/// `Result<(), Box<dyn Error>>`
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

	/// Set the primary (left side) Y-Axis to the given label and color.
	/// For secondary (right side) Y-Axis see [Self::set_secondary_y_axis].
	///
	/// # Arguments
	///
	/// * `chart`: The chart to add axis to.
	/// * `label`: Axis label.
	/// * `color`: Color of axis labels, or black by default.
	/// * `formatter`: Formatter of Y-Axis, that takes Y-Axis type and returns String.
	///
	/// # Returns
	/// `Result<(), Box<dyn Error>>`
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

	/// Set the secondary (right side) Y-Axis to the given label and color.
	/// For primary (left side) Y-Axis see [Self::set_y_axis].
	///
	/// # Arguments
	///
	/// * `chart`: The chart to add axis to.
	/// * `label`: Axis label.
	/// * `color`: Color of axis labels, or black by default.
	/// * `formatter`: Formatter of Y-Axis, that takes Y-Axis type and returns String.
	///
	/// # Returns
	/// `Result<(), Box<dyn Error>>`
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

	/// Draw a line series of provided data on the primary Y-Axis.
	/// For drawing on the secondary Y-Axis see [Self::draw_secondary_series].
	///
	/// # Arguments
	///
	/// * `chart`: The chart to draw on.
	/// * `data`: The data to draw.
	/// * `with_points`: Should circle points be made for each data plot?
	/// * `discontinue_line`: Should the line be continious/discontinue if part of the data is missing?
	/// * `label`: Legend label for the charted data.
	/// * `color`: Color of drawn line, or black by default.
	///
	/// # Returns
	/// `Result<(), Box<dyn Error>>`
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
		XT: Clone + Copy + Add<Output = XT> + PartialOrd + 'static + One,
		YT: Clone + 'static,
	{
		let color = color.unwrap_or(BLACK.to_rgba());

		// Split into data contigious data segments
		let data = if discontinue_line {
			split_data(data)
		} else {
			vec![data]
		};

		// Render
		let mut was_legend_defined = false;
		for split in data {
			let series = chart
				.draw_series(LineSeries::new(
					split.clone(),
					ShapeStyle {
						color: color.to_rgba(),
						filled: false,
						stroke_width: self.line_thickness,
					}
				))?;

			// Define only once
			if !was_legend_defined {
				was_legend_defined = true;
				series
					.label(label)
					.legend(move |(x, y)| PathElement::new(vec![(x, y), (x + 20, y)], color));
			}

			if with_points {
				chart.draw_series(PointSeries::of_element(
					split,
					3,
					color,
					&|c, s, st| Circle::new(c, s, st.filled()),
				))?;
			}
		}

		Ok(())
	}

	/// Draw a line series of provided data on the secondary Y-Axis.
	/// For drawing on the primary Y-Axis see [Self::draw_series].
	///
	/// # Arguments
	///
	/// * `chart`: The chart to draw on.
	/// * `data`: The data to draw.
	/// * `with_points`: Should circle points be made for each data plot?
	/// * `discontinue_line`: Should the line be continious/discontinue if part of the data is missing?
	/// * `label`: Legend label for the charted data.
	/// * `color`: Color of drawn line, or black by default.
	///
	/// # Returns
	/// `Result<(), Box<dyn Error>>`
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
		XT: Clone + Copy + Add<Output = XT> + PartialOrd + 'static + One,
		YT1: Clone + 'static,
		YT2: Clone + 'static,
	{
		let color = color.unwrap_or(BLACK.to_rgba());

		// Split into data contigious data segments
		let data = if discontinue_line {
			split_data(data)
		} else {
			vec![data]
		};

		// Render
		let mut was_legend_defined = false;
		for split in data {
			let series = chart
				.draw_secondary_series(LineSeries::new(
					split.clone(),
					ShapeStyle {
						color: color.to_rgba(),
						filled: false,
						stroke_width: self.line_thickness,
					}
				))?;

			// Define only once
			if !was_legend_defined {
				was_legend_defined = true;
				series
					.label(label)
					.legend(move |(x, y)| PathElement::new(vec![(x, y), (x + 20, y)], color));
			}

			if with_points {
				chart.draw_secondary_series(PointSeries::of_element(
					split,
					3,
					color,
					&|c, s, st| Circle::new(c, s, st.filled()),
				))?;
			}
		}

		Ok(())
	}

	/// Draw a legend in the bottom right corner.
	///
	/// # Arguments
	///
	/// * `chart`: The chart to draw on.
	///
	/// # Returns
	/// `Result<(), Box<dyn Error>>`
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
			.label_font(self.text_style.with_color(BLACK))
			.background_style(RGBAColor(180, 180, 180, 0.5))
			.position(SeriesLabelPosition::LowerRight)
			.draw()?;
		Ok(())
	}
}
