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

var IdrisInterface = function(element) {
	this.callbacks_ = [];
	this.events_ = [];
	this.element_ = element;
	this.grid_view_ = null;

	var that = this;
	element.addEventListener('keydown', function(e) {that.on_keydown_(e)});
};


IdrisInterface.prototype.on_keydown_ = function(e) {
	if (this.callbacks_.length > 0) {
		this.callbacks_.shift()(e['keyCode']);
	} else {
		this.events_.push(e);
	}
}

IdrisInterface.prototype.get_next_event = function(callback) {
	if (this.events_.length > 0) {
		var e = this.events_.shift();
		callback(this.events_.shift());	
	} else {
		this.callbacks_.push(callback);
	}	
}

IdrisInterface.prototype.init_display = function(rows, cols) {
	if (this.grid_view_ != null) {
		console.error('init_display can only be called once');
		return;
	}
	var options = {
		rows: rows,
		cols: cols
	};
	this.grid_view_ = new GridView(this.element_, options);
}

IdrisInterface.prototype.show = function(str) {
	if (this.grid_view_ == null) {
		console.error('init_display must be called before show');
		return;
	}
	this.grid_view_.show(str);
}

var idris_interface = new IdrisInterface(document.getElementById('game-area'));
