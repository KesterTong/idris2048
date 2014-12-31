var GridView = function(element, grid_size) {
	this.element_ = element;

	/**
	 * Array of grid cells, arranged in row major format
	 */
	this.cells_ = this.create_cells_(grid_size);
};

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

GridView.prototype.element = function() {
	return this.element_;
};

GridView.prototype.create_cells_ = function(grid_size) {
	var cells = [];
	for (var i = 0; i < grid_size; i++) {
		var row = document.createElement('div');
		row.className = 'row';
		for (var j = 0; j < grid_size; j++) {
			var cell = document.createElement('div');
			cell.className = 'cell';
			cells.push(cell);
			row.appendChild(cell);
		}
		this.element_.appendChild(row);
	}
	return cells;
};

var IdrisInterface = function(grid_view) {
	this.callbacks_ = [];
	this.events_ = [];
	this.grid_view_ = grid_view;

	var that = this;
	grid_view.element().addEventListener('keydown', function(e) {that.on_keydown_(e)});
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

IdrisInterface.prototype.show = function(str) {
	this.grid_view_.show(str);
}


var grid_view = new GridView(document.getElementById('game-area'), 4);

var idris_interface = new IdrisInterface(grid_view);
