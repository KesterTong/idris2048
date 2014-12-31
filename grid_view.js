/**
 * Manages the grid of cells.
 *
 * Creates an grid of cells, and updates the state of the grid according
 * to a string describing the state of each cell.
 *
 * @param {Element} element The DOM element that contains the view.
 * @param {Object} options Dictionary with the following keys:
 *    rows: The number of rows in the grid
 *    cols: The number of columns in the grid
 */
var GridView = function(element, options) {
	this.element_ = element;

	/**
	 * Array of grid cells, arranged in row major format
	 */
	this.cells_ = this.create_cells_(options.rows, options.cols);
};

/**
 * Update the view.
 * @param {string} str A string containing the state of
 *   each cell, in row major order.
 */
GridView.prototype.show = function(str) {
	if (str.length != this.cells_.length) {
		console.error('str had different length to the number of cells');
		return;
	}
	for (var i = 0; i < str.length; i++) {
		var cell_value = str.charCodeAt(i)
		var cell_html = cell_value == 0 ? '' : Math.pow(2, cell_value);
		this.cells_[i].innerHTML = cell_html;
	}
};

GridView.prototype.create_cells_ = function(rows, cols) {
	var cells = [];
	for (var i = 0; i < rows; i++) {
		var row = document.createElement('div');
		row.className = 'row';
		for (var j = 0; j < cols; j++) {
			var cell = document.createElement('div');
			cell.className = 'cell';
			cells.push(cell);
			row.appendChild(cell);
		}
		this.element_.appendChild(row);
	}
	return cells;
};